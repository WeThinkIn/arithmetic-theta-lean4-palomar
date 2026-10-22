module
public import Mathlib
import all Lean.Meta.Match.Match
macro "eu1295":command=> `(@[expose] public section)
macro "au1295":command=> `(set_option autoImplicit false)
macro "ru1295":command=> `(set_option backward.isDefEq.respectTransparency false)
macro "nu1295":command=> `(noncomputable section)
elab "ec979" n:num:command=> do
  for _ in [:n.getNat] do
    let ss ← Lean.Elab.Command.getScopes
    let h := ss.head!.header
    if h.isEmpty then Lean.Elab.Command.elabCommand (← `(end))
    else Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent (Lean.Name.str Lean.Name.anonymous h))))
eu1295 au1295 open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z7, SheafOfModules → z8, CommRingCat → z9, LinearMap → z10, ModuleCat → z11, AddMonoidHom → z12, RingHom → z13, IsDomain → z14, IsIntegrallyClosed → z15, Finsupp → z18, SetLike → z19, Submodule → z20, HomogeneousIdeal → z22, HomogeneousLocalization → z23, IsScalarTower → z25, AddSubgroupClass → z26, AddSubmonoidClass → z27, Algebra → z28, Nonempty → z29 open AlgebraicGeometry renaming Scheme → zS set_option maxHeartbeats 2000000 set_option maxRecDepth 8192 set_option backward.privateInPublic true macro "rc590":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}) set_option hygiene false set_option quotPrecheck false local notation "HG798x55" => (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) local notation "HG798x73" => (@z18.{0, 0} (Fin HG798x55) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) local notation "HG798x53" => (@ArithmeticThetaScaledTateBridgeR0046.PolynomialChart.{u_1} k inst)
local notation "HG798x34" => (@CommSemiring.toSemiring.{u_1} HG798x53 (@z0.toCommSemiring.{u_1} HG798x53 (@AddMonoidAlgebra.commRing.{u_1, 0} (ArithmeticThetaScaledTateBridgeR0046.Base.{u_1} k) HG798x73 (@MvPowerSeries.instCommRing.{0, u_1} Unit k (@z1.toCommRing.{u_1} k inst)) (@z18.instAddCommMonoid.{0, 0} (Fin HG798x55) Nat Nat.instAddCommMonoid)))) local notation "HG798x63" => (@ArithmeticThetaScaledTateBridgeR0046.relationIdeal.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) set_option quotPrecheck true set_option hygiene true eu1295
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
syntax (name:= p2mOpenIn) "p2m_open " str " in" ppLine command: command open Lean in macro_rules | `(p2m_open $s:str in $c:command) => return mkNullNode #[← `(section), ← `(p2m_open $s:str), c, ← `(end)] macro "p2m_open_scoped " s:str " in " c:command : command => `(section p2m_open_scoped $s $c end)    namespace AlgebraicGeometry ec979 1               namespace AlgebraicGeometry.Scheme ec979 2 namespace AlgebraicGeometry.Scheme.Hom ec979 3    namespace AlgebraicGeometry.Scheme.Modules ec979 3
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible ec979 4        namespace ArithmeticThetaAlgebraizedMarkedLineR0136 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion ec979 3    namespace ArithmeticThetaAnnularTorsionPrereqR0053 ec979 1    
 namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1    namespace ArithmeticThetaComponentDegreeR0184 ec979 1   namespace ArithmeticThetaCubicModelR0144 ec979 1 namespace ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144 ec979 2         
             
           
      namespace ArithmeticThetaGeneralEllipticKatoR0168 ec979 1  namespace ArithmeticThetaGenericEvaluationR0140 ec979 1 namespace ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140 ec979 2  namespace ArithmeticThetaGeometricLiftsR0141 ec979 1      
              namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1    
namespace ArithmeticThetaIdentitySectionsR0138 ec979 1   namespace ArithmeticThetaIndexedOverlapsR0058 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1  namespace ArithmeticThetaInvariantRatiosR0265 ec979 1             namespace ArithmeticThetaModelSymmetriesR0137 ec979 1  namespace ArithmeticThetaNodeCharts ec979 1    namespace ArithmeticThetaPolygonCartierR0133
ec979 1   namespace ArithmeticThetaPolygonCohomologyR0131 ec979 1 namespace ArithmeticThetaPositiveLineR0134 ec979 1   namespace ArithmeticThetaProjectiveEffectivityR0135 ec979 1       namespace ArithmeticThetaScaledAnnularR0050 ec979 1 namespace ArithmeticThetaScaledTateBridgeR0046 ec979 1  namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1  namespace ArithmeticThetaSchemeHodgeR0205 ec979 1   namespace ArithmeticThetaSchemeLevelR0204 ec979 1  
  namespace ArithmeticThetaSchemeThetaMarkingR0259 ec979 1      namespace ArithmeticThetaSharpCoverR0194 ec979 1  namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3    namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4   namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.Midpoint
ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4      namespace ArithmeticThetaTateCuspsR0181 ec979 1    namespace CategoryTheory ec979 1 namespace CategoryTheory.Limits ec979 2    namespace GoodReductionJacobian ec979 1   namespace HomogeneousIdealQuotientGrading ec979 1 namespace NeronModelInfra ec979 1   namespace P2MW ec979 1 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso ec979 2   
   namespace PresheafOfModules ec979 1 namespace PresheafOfModules.InternalHom ec979 2 namespace PresheafOfModules.PullbackMonoidal ec979 2              namespace ProjWeierstrassCubicPrime ec979 1 namespace SheafOfModules ec979 1 namespace WeierstrassCurve ec979 1  namespace WeierstrassProjModel ec979 1  namespace HomogeneousIdealQuotientGrading ec979 1 namespace NeronModelInfra ec979 1 section rc590 eu1295 au1295 namespace WeierstrassProjModel  ec979 1
au1295 universe u namespace WeierstrassProjModel  ec979 1 nu1295 open AlgebraicGeometry CategoryTheory MvPolynomial open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime open NeronModelInfra namespace WeierstrassProjModel attribute [local instance] z6.gradedAlgebra section Carrier variable {R: Type*} [z0 R] theorem span_polynomial_isHomogeneousCR (V: z3.Projective R): (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R):= by sorry def projModelHomogeneousIdealCR (V: z3.Projective R): z22 (homogeneousSubmodule (Fin 3) R):= ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩ @[simp] theorem projModelHomogeneousIdealCR_toIdeal (V: z3.Projective R): (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial}:= by sorry ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 namespace WeierstrassProjModel ec979 1 section rc590 eu1295 au1295 ru1295 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
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
@[simp] lemma smul_app {X: Cᵒᵖ} (r: R.obj X) (φ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (r • φ).1 f x = R.map f r • φ.1 f x:= by sorry @[simp] lemma add_app {X: Cᵒᵖ} (φ ψ: naturalFamilies F N X) {Y: Cᵒᵖ} (f: X ⟶ Y) (x: F.obj Y): (φ + ψ).1 f x = φ.1 f x + ψ.1 f x:= by sorry set_option hygiene false set_option quotPrecheck false
local notation "Hg1" => (@CategoryTheory.Functor.comp.{u_3, u_1, u_1, u_2, u_1 + 1, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} R (@CategoryTheory.forget₂.{u_1, u_1, u_1 + 1, u_1, u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (fun (R S : CommRingCat.{u_1}) => @RingHom.{u_1, u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} R) (CommRingCat.commRing.{u_1} R)))) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} S) (CommRingCat.commRing.{u_1} S))))) CommRingCat.carrier.{u_1} (fun (X Y : CommRingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} X) ((fun (X : CommRingCat.{u_1}) => @CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} X) (CommRingCat.commRing.{u_1} X))) X)) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Y) (CommRingCat.commRing.{u_1} Y))))) CommRingCat.instConcreteCategoryRingHomCarrier.{u_1} RingCat.{u_1} RingCat.instCategory.{u_1} (fun (R S : RingCat.{u_1}) => @RingHom.{u_1, u_1} (RingCat.carrier.{u_1} R) (RingCat.carrier.{u_1} S) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} R) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} R) (RingCat.ring.{u_1} R))) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} S) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} S) (RingCat.ring.{u_1} S)))) RingCat.carrier.{u_1} (fun (X Y : RingCat.{u_1}) => @RingHom.instFunLike.{u_1, u_1} (RingCat.carrier.{u_1} X) (RingCat.carrier.{u_1} Y) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} X) ((fun (X : RingCat.{u_1}) => @Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} X) (RingCat.ring.{u_1} X)) X)) (@Semiring.toNonAssocSemiring.{u_1} (RingCat.carrier.{u_1} Y) (@Ring.toSemiring.{u_1} (RingCat.carrier.{u_1} Y) (RingCat.ring.{u_1} Y)))) RingCat.instConcreteCategoryRingHomCarrier.{u_1} CommRingCat.hasForgetToRingCat.{u_1}))
local notation "Hg5" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 i) local notation "Hg38" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F i) local notation "Hg21" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38) local notation "Hg39" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N i) local notation "Hg4" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R i) local notation "Hg33" => (@CommRing.toRing.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4)) local notation "Hg52" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg39) local notation "Hg51" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) Hg33 Hg38) local notation "Hg17" => (@AddCommGroup.toAddCommMonoid.{u_1} Hg21 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38)) local notation "Hg12" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg4)))
local notation "Hg27" => (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg4) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg4) Hg12)) local notation "Hg23" => (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39) local notation "Hg32" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39) local notation "Hg31" => (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg38) local notation "Hg19" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg5) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg5) Hg39) local notation "Hg11" => (@LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32) local notation "Hg22" => (@Quiver.opposite.{u_2, u_3} C (@CategoryTheory.ReflQuiver.toQuiver.{u_3, u_2} C (@CategoryTheory.catToReflQuiver.{u_3, u_2} C inst))) local notation "Hg48" => (@Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) local notation "Hg14" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R Y)
local notation "Hg30" => (@CommSemiring.toSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRing.toCommSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg14))) local notation "Hg47" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 N Y) local notation "Hg46" => (@PresheafOfModules.obj.{u_1, u_3, u_2, u_1} C inst Hg1 F Y) local notation "Hg15" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) RingCat.{u_1} RingCat.instCategory.{u_1} Hg1 Y) local notation "Hg42" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47) local notation "Hg41" => (@ModuleCat.carrier.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)
local notation "Hg6" => (fun (Y : Opposite.{u_2 + 1} C) => @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X Y → @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (CommRingCat.carrier.{u_1} Hg14) Hg30 Hg30 (@RingHom.id.{u_1} (CommRingCat.carrier.{u_1} Hg14) (@Semiring.toNonAssocSemiring.{u_1} (CommRingCat.carrier.{u_1} Hg14) Hg30)) Hg41 Hg42 (@AddCommGroup.toAddCommMonoid.{u_1} Hg41 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46)) (@AddCommGroup.toAddCommMonoid.{u_1} Hg42 (@ModuleCat.isAddCommGroup.{u_1, u_1} (RingCat.carrier.{u_1} Hg15) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg46) (@ModuleCat.isModule.{u_1, u_1} (CommRingCat.carrier.{u_1} Hg14) (@RingCat.instRingObjForgetRingHomCarrier.{u_1} Hg15) Hg47)) local notation "Hg10" => (fun (x : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => @LinearMap.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg12 Hg12 Hg27 Hg21 Hg19 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg31 Hg32)
local notation "Hg0" => (@Pi.addGroup.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addGroup.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg51 Hg52 Hg27)) i) local notation "Hg13" => (@PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) local notation "Hg45" => (@AddSubgroup.instSetLike.{max (max u_1 u_2) u_3} Hg13 Hg0) local notation "Hg29" => (@PresheafOfModules.InternalHom.naturalFamilies.{u_1, u_3, u_2} C inst R F N X)
local notation "Hg2" => (@AddSubmonoidClass.toAddCommMonoid.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@Pi.addCommMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.addCommMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @LinearMap.addCommMonoid.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 (@AddCommGroup.toAddCommMonoid.{u_1} Hg19 Hg23) Hg51 Hg52 Hg27) i) (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg45 (@AddSubgroupClass.toAddSubmonoidClass.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 (@Pi.subNegMonoid.{u_2, max u_1 u_3} (Opposite.{u_2 + 1} C) Hg6 fun (i : Opposite.{u_2 + 1} C) => @Pi.subNegMonoid.{u_3, u_1} Hg48 Hg10 fun (i_1 : @Quiver.Hom.{u_3, u_2} (Opposite.{u_2 + 1} C) Hg22 X i) => (fun (i : Opposite.{u_2 + 1} C) => @AddGroup.toSubNegMonoid.{u_1} Hg11 (@AddCommGroup.toAddGroup.{u_1} Hg11 (@LinearMap.addCommGroup.{u_1, u_1, u_1, u_1} (CommRingCat.carrier.{u_1} Hg4) (CommRingCat.carrier.{u_1} Hg4) Hg21 Hg19 Hg12 Hg12 Hg17 Hg23 Hg31 Hg32 Hg27))) i) Hg45 (@AddSubgroup.instAddSubgroupClass.{max (max u_1 u_2) u_3} Hg13 Hg0)) Hg29) local notation "Hg20" => (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg13 Hg45)
local notation "Hg3" => (@Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x) local notation "Hg18" => (@CategoryTheory.Functor.obj.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1} R X) local notation "Hg7" => (CommRingCat.carrier.{u_1} Hg18) local notation "Hg16" => (@instHSMul.{u_1, max (max u_1 u_2) u_3} Hg7 Hg3 (@PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies.{u_1, u_3, u_2} C inst R F N X)) local notation "Hg26" => (@OfNat.ofNat.{max (max u_1 u_2) u_3} Hg3 (nat_lit 0) (@Zero.toOfNat0.{max (max u_1 u_2) u_3} Hg3 (@AddZero.toZero.{max (max u_1 u_2) u_3} Hg3 (@AddZeroClass.toAddZero.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddZeroClass.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2)))))) local notation "Hg28" => (@CommSemiring.toSemiring.{u_1} Hg7 (@CommRing.toCommSemiring.{u_1} Hg7 (@CommRingCat.instCommRingObjForgetRingHomCarrier.{u_1} Hg18))) local notation "Hg40" => (@instHAdd.{max (max u_1 u_2) u_3} Hg3 (@AddSemigroup.toAdd.{max (max u_1 u_2) u_3} Hg3 (@AddMonoid.toAddSemigroup.{max (max u_1 u_2) u_3} Hg3 (@AddCommMonoid.toAddMonoid.{max (max u_1 u_2) u_3} Hg3 Hg2))))
local notation "Hg49" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 s φ) local notation "Hg50" => (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r φ) set_option quotPrecheck true set_option hygiene true theorem _root_.PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies._proof_1.{u_1,u_2,u_3} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {R : @CategoryTheory.Functor.{u_3, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_3, u_2} C inst) CommRingCat.{u_1} CommRingCat.instCategory.{u_1}} {F N : @PresheafOfModules.{u_1, u_3, u_2, u_1} C inst Hg1} (X : Opposite.{u_2 + 1} C) (r s : CommRingCat.carrier.{u_1} Hg18) (φ : @Subtype.{(max (max u_1 u_2) u_3) + 1} Hg13 fun (x : @PresheafOfModules.InternalHom.PiFamily.{u_1, u_3, u_2} C inst R F N X) => @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg13 (@AddSubgroup.{max (max u_2 u_3) u_1} Hg13 Hg0) Hg20 Hg29 x), @Eq.{(max (max u_1 u_2) u_3) + 1} Hg3 (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 (@HMul.hMul.{u_1, u_1, u_1} Hg7 Hg7 Hg7 (@instHMul.{u_1} Hg7 (@Semigroup.toMul.{u_1} Hg7 (@Monoid.toSemigroup.{u_1} Hg7 (@Semiring.toMonoid.{u_1} Hg7 Hg28)))) r s) φ) (@HSMul.hSMul.{u_1, max (max u_1 u_2) u_3, max (max u_1 u_2) u_3} Hg7 Hg3 Hg3 Hg16 r Hg49) := by sorry
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
ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false au1295 universe u open CategoryTheory MonoidalCategory Limits nu1295 namespace SheafOfModules variable {C: Type u} [Category.{u} C] {J: GrothendieckTopology C} (𝒪: Cᵒᵖ ⥤ z9.{u}) (h𝒪: Presheaf.IsSheaf J (𝒪 ⋙ forget₂ z9 RingCat)) [originalWEquals: J.WEqualsLocallyBijective AddCommGrpCat.{u}] [originalWeakSheafify: HasWeakSheafify J AddCommGrpCat.{u}] abbrev ringSheaf: Sheaf J RingCat.{u}:= ⟨𝒪 ⋙ forget₂ z9 RingCat, h𝒪⟩ abbrev PMod:= z7.{u} (𝒪 ⋙ forget₂ z9 RingCat)
abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
abbrev toPMod: z8.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪:= z8.forget (ringSheaf 𝒪 h𝒪) ⋙ z7.restrictScalars (𝟙 (𝒪 ⋙ forget₂ z9 RingCat))
abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
instance instFaithfulRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Faithful:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instFullRingSheafPModToPMod: (toPMod 𝒪 h𝒪).Full:= by exact (fun (_: J.WEqualsLocallyBijective AddCommGrpCat.{u}) (_: HasWeakSheafify J AddCommGrpCat.{u}) => (by sorry)) originalWEquals originalWeakSheafify instance instIsLocalizationPModRingSheafSheafifyFunctorPresheafW: (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪):= by sorry include h𝒪 in theorem presheafW_isMonoidal: (presheafW J 𝒪).IsMonoidal:= by sorry def sheafifyCounitIso (M: z8.{u} (ringSheaf 𝒪 h𝒪)): (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M:= (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] ru1295 in def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅ (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) := sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))
instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal
instance monoidalClosed: MonoidalClosed (z8.{u} (ringSheaf 𝒪 h𝒪)):= Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪) ec979 1 namespace AlgebraicGeometry variable (X: Scheme.{u}) instance Scheme.PresheafOfModulesOfCommRing.monoidalCategory: MonoidalCategory X.PresheafOfModules:= inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ z9 RingCat))) instance Scheme.Modules.monoidalCategory: MonoidalCategory X.Modules:= inferInstanceAs (MonoidalCategory (z8.{u} (z8.ringSheaf X.sheaf.obj X.ringCatSheaf.property))) instance Scheme.Modules.monoidalClosed: MonoidalClosed X.Modules:= inferInstanceAs (MonoidalClosed (z8.{u} (z8.ringSheaf X.sheaf.obj X.ringCatSheaf.property))) variable {X} abbrev Scheme.Modules.dual (L: X.Modules): X.Modules:= (ihom L).obj (𝟙_ X.Modules) variable (X) in abbrev Scheme.Modules.sheafify: X.PresheafOfModules ⥤ X.Modules:= z8.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property instance instMonoidalPresheafOfModulesModulesSheafify: (Scheme.Modules.sheafify X).Monoidal:= inferInstanceAs (z8.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).Monoidal ec979 1 ec979 1 ec979 1 ec979 1 namespace AlgebraicGeometry.Scheme.Modules ec979 3 section rc590 eu1295 set_option backward.isDefEq.respectTransparency.types false au1295 ru1295 set_option backward.isDefEq.respectTransparency.instanceSearchTypes false universe v u v₁ u₁ v₂ u₂ open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal
namespace PresheafOfModules section restrictScalars variable {C: Type u₁} [Category.{v₁} C] {R S: Cᵒᵖ ⥤ z9.{u}} (φ: S ⟶ R) abbrev ringCatHom: S ⋙ forget₂ z9 RingCat ⟶ R ⋙ forget₂ z9 RingCat:= Functor.whiskerRight φ (forget₂ z9 RingCat) noncomputable abbrev restrictScalarsAt (U: Cᵒᵖ): z11.{u} (R.obj U) ⥤ z11.{u} (S.obj U):= z11.restrictScalars (φ.app U).hom
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
instance isIso_δ (A B: z7.{u} S'): IsIso (δ (pb F φ) A B):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts instance isIso_η: IsIso (η (pb F φ)):= by exact (fun (_: HasFiniteProducts C) (_: HasFiniteProducts D) (_: PreservesFiniteProducts F) => (by sorry)) originalProductsC originalProductsD originalPreservesProducts noncomputable instance pullback_monoidal: (pb F φ).Monoidal:= Functor.Monoidal.ofOplaxMonoidal _ ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 ru1295 universe u open CategoryTheory MonoidalCategory Limits TopologicalSpace nu1295 namespace AlgebraicGeometry.Scheme.Modules variable {X Y: Scheme.{u}} (f: X ⟶ Y)
instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) := by sorry
instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) := by sorry
instance preservesFiniteProducts_opensMap: PreservesFiniteProducts (Opens.map f.base) := by sorry
abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c
instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base)
    (R := X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf) (S := Y.sheaf.obj) f.c).Monoidal
variable (Y) in instance sheafify_isLocalization': (Modules.sheafify Y).IsLocalization (z8.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj):= by sorry instance instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback: Localization.Lifting (Modules.sheafify Y) (z8.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f):= ⟨z8.sheafificationCompPullback f.toRingCatSheafHom⟩
instance pullback_monoidal : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
def pullbackTensorObjIso (L M: Y.Modules): (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M:= (Functor.Monoidal.μIso (Modules.pullback f) L M).symm ec979 3 ec979 1 ec979 1 ec979 1 namespace AlgebraicGeometry.Scheme.Modules ec979 3 section rc590 eu1295 ru1295 au1295 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open NeronModelInfra nu1295 namespace AlgebraicGeometry structure Scheme.Modules.IsInvertible {X: Scheme.{u}} (M: X.Modules): Prop where (exists_trivialization: ∀ x: X, ∃ (U: X.Opens), x ∈ U ∧ z29 ((Scheme.Modules.pullback U.ι).obj M ≅ z8.unit U.toScheme.ringCatSheaf)) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 ru1295 universe u open CategoryTheory TopologicalSpace Opposite nu1295 namespace AlgebraicGeometry.Scheme.Modules variable {X Y: Scheme.{u}} (φ: X ⟶ Y) section variable {L: Y.Modules} {U: Y.Opens} def pullbackLocalSection (s: Γ(L, U)): Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U):= ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s ec979 1 ec979 3 ec979 1 ec979 1 ec979 1 namespace GoodReductionJacobian  ec979 1 namespace GoodReductionJacobian  ec979 1 namespace AlgebraicGeometry  ec979 1 namespace AlgebraicGeometry
 ec979 1  namespace AlgebraicGeometry  namespace OModulePresheaf ec979 1 ec979 1 namespace AlgebraicGeometry  namespace OModulePresheaf namespace Hom ec979 1  ec979 1 ec979 1  namespace AlgebraicGeometry.Scheme.Hom ec979 3  section rc590 eu1295 au1295 ru1295 nu1295 universe u namespace ArithmeticThetaNodeCharts variable (k: Type u) [z1 k] abbrev Base:= z4 k def parameter: Base k:= z4.X abbrev PolynomialChart:= z6 (Fin 2) (Base k) def relation: PolynomialChart k:= z6.X 0 * z6.X 1 - z6.C (parameter k) def relationIdeal: Ideal (PolynomialChart k):= Ideal.span {relation k} abbrev Node:= PolynomialChart k ⧸ relationIdeal k
instance (priority := 2000) nodeCommRing : CommRing (Node k) :=
  Ideal.Quotient.commRing (relationIdeal k)
def quotientMap: PolynomialChart k →+* Node k:= Ideal.Quotient.mk (relationIdeal k) def x: Node k:= quotientMap k (z6.X 0) def y: Node k:= quotientMap k (z6.X 1) def t: Node k:= algebraMap (Base k) (Node k) (parameter k) abbrev Torus:= LaurentPolynomial (Base k) def torusMap: PolynomialChart k →+* Torus k:= z6.eval₂Hom LaurentPolynomial.C (fun i => if i = (0: Fin 2) then LaurentPolynomial.T 1 else LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) def oppositeTorusMap: PolynomialChart k →+* Torus k:= z6.eval₂Hom LaurentPolynomial.C (fun i => if i = (0: Fin 2) then LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1) else LaurentPolynomial.T 1) abbrev XChart:= Localization.Away (x k) abbrev YChart:= Localization.Away (y k) def toXChart: Node k →+* XChart k:= algebraMap (Node k) (XChart k) def toYChart: Node k →+* YChart k:= algebraMap (Node k) (YChart k) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 set_option maxHeartbeats 400000 nu1295 universe u namespace ArithmeticThetaNodeCharts variable (k: Type u) [z1 k] theorem node_torus_chart_equivalences: ∀ (k: Type u) [z1 k] [z2 k], (∃! e: XChart k ≃+* Torus k, e.toRingHom.comp ((toXChart k).comp (quotientMap k)) = torusMap k) ∧ (∃! e: YChart k ≃+* Torus k, e.toRingHom.comp ((toYChart k).comp (quotientMap k)) = oppositeTorusMap k):= by sorry ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 set_option maxHeartbeats 800000 nu1295 universe u
namespace ArithmeticThetaScaledTateBridgeR0046 variable (k: Type u) [z1 k] abbrev Base:= z4 k def parameter (r: ℕ): Base k:= z4.X ^ r abbrev PolynomialChart:= z6 (Fin 2) (Base k) def relation (r: ℕ): PolynomialChart k:= z6.X 0 * z6.X 1 - z6.C (parameter k r) def relationIdeal (r: ℕ): Ideal (PolynomialChart k):= Ideal.span {relation k r} abbrev Node (r: ℕ):= PolynomialChart k ⧸ relationIdeal k r instance instCommRingNode (r: ℕ): z0 (Node k r):= Ideal.Quotient.commRing (relationIdeal k r) def t (r: ℕ): Node k r:= algebraMap (Base k) (Node k r) (parameter k r) def nodeIdeal (r: ℕ): Ideal (Node k r):= Ideal.span {t k r} abbrev CompletedNode (r: ℕ):= AdicCompletion (nodeIdeal k r) (Node k r) def toCompleted (r: ℕ): Node k r →+* CompletedNode k r:= algebraMap _ _ def completedBaseMap (r: ℕ): Base k →+* CompletedNode k r:= (toCompleted k r).comp (algebraMap (Base k) (Node k r)) def completedParameter (r: ℕ): CompletedNode k r:= toCompleted k r (t k r) def completedPower (r n: ℕ): Ideal (CompletedNode k r):= (Ideal.span {completedParameter k r}) ^ n ec979 1 ec979 1 ec979 1 ec979 1   section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaScaledAnnularR0050 open ArithmeticThetaScaledTateBridgeR0046 variable (k: Type u) [z1 k] def tau (r: ℕ): CompletedNode k r:= completedBaseMap k r z4.X variable [z2 k] ec979 1 ec979 1 ec979 1 ec979 1 section rc590
eu1295 au1295 nu1295 universe u namespace ArithmeticThetaAnnularTorsionPrereqR0053 variable (k: Type u) [z1 k] [z2 k] abbrev Base:= z4 k abbrev Node:= ArithmeticThetaScaledTateBridgeR0046.Node k 1 abbrev Chart:= ArithmeticThetaScaledTateBridgeR0046.CompletedNode k 1 def nodeBase: Base k →+* Node k:= algebraMap _ _ def complete: Node k →+* Chart k:= ArithmeticThetaScaledTateBridgeR0046.toCompleted k 1 def tau: Chart k:= ArithmeticThetaScaledAnnularR0050.tau k 1 def filtration (n: ℕ): Ideal (Chart k):= ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 n ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaIndexedOverlapsR0058 variable (k: Type u) [z1 k] [z2 k] abbrev Base:= z4 k abbrev Node (_j: ℕ):= ArithmeticThetaNodeCharts.Node k abbrev Chart (_j: ℕ):= ArithmeticThetaAnnularTorsionPrereqR0053.Chart k def next (r j: ℕ): ℕ:= (j + 1) % r def nodeCoord (side: Bool): Node k 0:= if side then ArithmeticThetaNodeCharts.x k else ArithmeticThetaNodeCharts.y k abbrev Open (_j: ℕ) (side: Bool):= Localization.Away (nodeCoord k side)
theorem _root_.ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_1.{u_1}: ∀ (k: Type u_1) [inst: z1.{u_1} k], @Eq.{u_1 + 1} (@Ideal.{u_1} HG798x53 (@AddMonoidAlgebra.semiring.{u_1, 0} (ArithmeticThetaScaledTateBridgeR0046.Base.{u_1} k) HG798x73 (@CommSemiring.toSemiring.{u_1} (ArithmeticThetaScaledTateBridgeR0046.Base.{u_1} k) (@MvPowerSeries.instCommSemiring.{0, u_1} Unit k (@Semifield.toCommSemiring.{u_1} k (@z1.toSemifield.{u_1} k inst)))) (@z18.instAddMonoid.{0, 0} (Fin HG798x55) Nat Nat.instAddMonoid))) HG798x63 (@ArithmeticThetaNodeCharts.relationIdeal.{u_1} k inst):= by sorry theorem _root_.ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_2.{u_1}: ∀ (k: Type u_1) [inst: z1.{u_1} k], @Ideal.IsTwoSided.{u_1} HG798x53 HG798x34 HG798x63:= by sorry theorem _root_.ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_3.{u_1}: ∀ (k: Type u_1) [inst: z1.{u_1} k], @Ideal.IsTwoSided.{u_1} HG798x53 HG798x34 (@ArithmeticThetaNodeCharts.relationIdeal.{u_1} k inst):= by sorry
run_cmd do
  for n in [`ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_1, `ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_2, `ArithmeticThetaIndexedOverlapsR0058.nodeEquiv._proof_3] do
    let ci ← Lean.getConstInfo n
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
def nodeEquiv : ArithmeticThetaAnnularTorsionPrereqR0053.Node k ≃+* Node k 0 :=
  (Ideal.quotientEquivAlgOfEq (Base k) (show
    ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter])).toRingEquiv
def openMap (j: ℕ) (side: Bool): ArithmeticThetaAnnularTorsionPrereqR0053.Node k →+* Open k j side:= (algebraMap (Node k j) (Open k j side)).comp (nodeEquiv k).toRingHom def openBase (j: ℕ) (side: Bool): Base k →+* Open k j side:= (openMap k j side).comp (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k) def ot (j: ℕ) (side: Bool): Open k j side:= openBase k j side z4.X
def torusEquiv (j : ℕ) (side : Bool) : Open k j side ≃+* ArithmeticThetaNodeCharts.Torus k := by
  cases side with
  | false => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).2
  | true => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
def adjacent (r j: ℕ): Open k j false ≃+* Open k (next r j) true:= ((torusEquiv k j false).trans LaurentPolynomial.invert.toRingEquiv).trans (torusEquiv k (next r j) true).symm def openIdeal (j: ℕ) (side: Bool): Ideal (Open k j side):= Ideal.span {ot k j side} abbrev OpenHat (j: ℕ) (side: Bool):= AdicCompletion (openIdeal k j side) (Open k j side) def completeOpen (j: ℕ) (side: Bool): Open k j side →+* OpenHat k j side:= algebraMap _ _ def hatPower (j: ℕ) (side: Bool) (n: ℕ): Ideal (OpenHat k j side):= (Ideal.span {completeOpen k j side (ot k j side)}) ^ n def IsRestriction (j: ℕ) (side: Bool) (R: Chart k j →+* OpenHat k j side): Prop:= R.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) = (completeOpen k j side).comp (openMap k j side) ∧ ∀ n f, f ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n → R f ∈ hatPower k j side n ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 set_option backward.privateInPublic true ru1295 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false set_option synthInstance.maxHeartbeats 200000 au1295 set_option maxHeartbeats 1200000 nu1295 universe u namespace ArithmeticThetaIndexedOverlapsR0058 open ArithmeticThetaAnnularTorsionPrereqR0053 variable (k: Type u) [z1 k] [z2 k]
theorem completed_coordinate_restrictions: ∀ (k: Type u) [z1 k] [z2 k] (j: ℕ) (side: Bool), ∃! R: Chart k j →+* OpenHat k j side, IsRestriction k j side R:= by sorry ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaInfinitesimalPolygonR0129 open CategoryTheory abbrev Trunc (R: Type u) [z0 R] (t: R) (n: ℕ):= R ⧸ (Ideal.span {t}) ^ (n+1) def trunc (R: Type u) [z0 R] (t: R) (n: ℕ): R →+* Trunc R t n:= Ideal.Quotient.mk _
def truncMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (t : R) (s : S) (h : f t = s) (n : ℕ) : Trunc R t n →+* Trunc S s n :=
  Ideal.quotientMap _ f (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, h])
def truncReduce (R: Type u) [z0 R] (t: R) (n N: ℕ) (h: n ≤ N): Trunc R t N →+* Trunc R t n:= Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) variable (k: Type u) [z1 k] [z2 k] abbrev R (n: ℕ):= Trunc (z4 k) z4.X n abbrev A (n: ℕ):= Trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n abbrev RawOpen (side: Bool):= ArithmeticThetaIndexedOverlapsR0058.Open k 0 side def openParameter (side: Bool): RawOpen k side:= algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side) (ArithmeticThetaNodeCharts.t k) abbrev B (n: ℕ) (side: Bool):= Trunc (RawOpen k side) (openParameter k side) n def base (n: ℕ): R k n →+* A k n:= truncMap (algebraMap (z4 k) (ArithmeticThetaNodeCharts.Node k)) z4.X (ArithmeticThetaNodeCharts.t k) rfl n def restriction (n: ℕ) (side: Bool): A k n →+* B k n side:= truncMap (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side)) (ArithmeticThetaNodeCharts.t k) (openParameter k side) rfl n def rawAdjacent: RawOpen k false ≃+* RawOpen k true:= ArithmeticThetaIndexedOverlapsR0058.adjacent k 1 0 def IsAdjacent (n: ℕ) (E: B k n false ≃+* B k n true): Prop:= E.toRingHom.comp (trunc (RawOpen k false) (openParameter k false) n) = (trunc (RawOpen k true) (openParameter k true) n).comp (rawAdjacent k).toRingHom abbrev Hat:= ArithmeticThetaAnnularTorsionPrereqR0053.Chart k abbrev HatA (n: ℕ):= Trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n abbrev HatOpen (side: Bool):= ArithmeticThetaIndexedOverlapsR0058.OpenHat k 0 side
abbrev HatB (n: ℕ) (side: Bool):= Trunc (HatOpen k side) (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n def CompletionComparison (n: ℕ) (e: HatA k n ≃+* A k n) (o: ∀ side: Bool, HatB k n side ≃+* B k n side): Prop:= e.toRingHom.comp ((trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n).comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)) = (trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n).comp (ArithmeticThetaIndexedOverlapsR0058.nodeEquiv k).toRingHom ∧ (∀ side: Bool, (o side).toRingHom.comp ((trunc (HatOpen k side) (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n).comp (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side)) = trunc (RawOpen k side) (openParameter k side) n) ∧ (∀ (side: Bool) (s: Hat k), o side (trunc (HatOpen k side) (ArithmeticThetaIndexedOverlapsR0058.completeOpen k 0 side (openParameter k side)) n (Classical.choose (ArithmeticThetaIndexedOverlapsR0058.completed_coordinate_restrictions k 0 side) s)) = restriction k n side (e (trunc (Hat k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n s))) def specR (n: ℕ): zS.{u}:= AlgebraicGeometry.Spec (z9.of (R k n)) def specA (n: ℕ): zS.{u}:= AlgebraicGeometry.Spec (z9.of (A k n)) def specB (n: ℕ) (side: Bool): zS.{u}:= AlgebraicGeometry.Spec (z9.of (B k n side)) def structureMap (n: ℕ): specA k n ⟶ specR k n:= AlgebraicGeometry.Spec.map (z9.ofHom (base k n))
def rightLeg (n: ℕ): specB k n true ⟶ specA k n:= AlgebraicGeometry.Spec.map (z9.ofHom (restriction k n true)) def leftLeg (n: ℕ) (E: B k n false ≃+* B k n true): specB k n true ⟶ specA k n:= AlgebraicGeometry.Spec.map (z9.ofHom (E.toRingHom.comp (restriction k n false))) def next (r: ℕ) (hr: 0 < r) (i: Fin r): Fin r:= ⟨(i.val+1)%r, Nat.mod_lt _ hr⟩ structure Atlas (r n: ℕ) (hr: 0 < r) (E: B k n false ≃+* B k n true) where (X: zS.{u}) (p: X ⟶ specR k n) (chart: Fin r → (specA k n ⟶ X)) (chart_open: ∀ i, AlgebraicGeometry.IsOpenImmersion (chart i)) (covers: ∀ x: X, ∃ (i: Fin r) (a: specA k n), chart i a = x) (chart_over: ∀ i, chart i ≫ p = structureMap k n) (adjacent: ∀ i, CategoryTheory.IsPullback (leftLeg k n E) (rightLeg k n) (chart i) (chart (next r hr i))) (disjoint: ∀ i j, i ≠ j → next r hr i ≠ j → next r hr j ≠ i → Disjoint (Set.range (chart i)) (Set.range (chart j))) def baseReduction (n N: ℕ) (h: n ≤ N): specR k n ⟶ specR k N:= AlgebraicGeometry.Spec.map (z9.ofHom (truncReduce (z4 k) z4.X n N h)) def chartReduction (n N: ℕ) (h: n ≤ N): specA k n ⟶ specA k N:= AlgebraicGeometry.Spec.map (z9.ofHom (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h)) def IsReduction (r n N: ℕ) (hr: 0 < r) (h: n ≤ N) {E: B k n false ≃+* B k n true} {F: B k N false ≃+* B k N true} (D: Atlas k r n hr E) (T: Atlas k r N hr F) (i: D.X ⟶ T.X): Prop:= i ≫ T.p = D.p ≫ baseReduction k n N h ∧ ∀ j: Fin r, D.chart j ≫ i = chartReduction k n N h ≫ T.chart j
structure Tower (r: ℕ) (hr: 0 < r) where (overlap: ∀ n, B k n false ≃+* B k n true) (overlap_spec: ∀ n, IsAdjacent k n (overlap n)) (atlas: ∀ n, Atlas k r n hr (overlap n)) (transition: ∀ n N (h: n ≤ N), (atlas n).X ⟶ (atlas N).X) (transition_spec: ∀ n N h, IsReduction k r n N hr h (atlas n) (atlas N) (transition n N h)) (identity: ∀ n, transition n n (le_refl n) = 𝟙 (atlas n).X) (composition: ∀ n N P (h: n ≤ N) (h': N ≤ P), transition n N h ≫ transition N P h' = transition n P (le_trans h h')) ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaInfinitesimalPolygonR0129 ec979 1 namespace ArithmeticThetaPolygonCohomologyR0131 ec979 1 section rc590 eu1295 au1295 ru1295 nu1295 universe u namespace ArithmeticThetaPolygonCartierR0133 open CategoryTheory AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaPolygonCohomologyR0131 variable (k: Type u) [z1 k] [z2 k] set_option hygiene false set_option quotPrecheck false local notation "Hu9" => (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} Y))) local notation "Hu0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu9)
local notation "Hu10" => (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X))) local notation "Hu1" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu10) local notation "Hu5" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0)) local notation "Hu2" => (@Preorder.smallCategory.{u_1} Hu5 (@PartialOrder.toPreorder.{u_1} Hu5 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0)))) local notation "Hu6" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1)) local notation "Hu3" => (@Preorder.smallCategory.{u_1} Hu6 (@PartialOrder.toPreorder.{u_1} Hu6 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1)))) local notation "Hu4" => (@TopologicalSpace.Opens.map.{u_1} Hu1 Hu0 (@AlgebraicGeometry.PresheafedSpace.Hom.base.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} Hu10 Hu9 (@AlgebraicGeometry.LocallyRingedSpace.Hom.toHom.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X) (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} Y) (@AlgebraicGeometry.Scheme.Hom.toLRSHom'.{u_1} X Y f)))) local notation "Hu7" => (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} Hu0) (TopCat.str.{u_1} Hu0))
local notation "Hu8" => (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} Hu1) (TopCat.str.{u_1} Hu1)) local notation "Hu11" => (@CategoryTheory.ReflQuiver.toQuiver.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} (@CategoryTheory.catToReflQuiver.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} AlgebraicGeometry.Scheme.instCategory.{u_1})) set_option quotPrecheck true set_option hygiene true theorem _root_.ArithmeticThetaPolygonCartierR0133.unitPullback._proof_1.{u_1} : ∀ {X Y : AlgebraicGeometry.Scheme.{u_1}} (f : @Quiver.Hom.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} Hu11 X Y), @CategoryTheory.Functor.IsContinuous.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu6 Hu3 Hu4 Hu7 Hu8 := by sorry
theorem _root_.ArithmeticThetaPolygonCartierR0133.unitPullback._proof_2.{u_1} : ∀ {X Y : AlgebraicGeometry.Scheme.{u_1}} (f : @Quiver.Hom.{u_1, u_1 + 1} AlgebraicGeometry.Scheme.{u_1} Hu11 X Y), @CategoryTheory.Functor.IsRightAdjoint.{u_1, u_1, u_1 + 1, u_1 + 1} (@SheafOfModules.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu7 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y)) (@SheafOfModules.instCategory.{u_1, u_1, u_1, u_1} Hu5 Hu2 Hu7 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y)) (@SheafOfModules.{u_1, u_1, u_1, u_1} Hu6 Hu3 Hu8 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X)) (@SheafOfModules.instCategory.{u_1, u_1, u_1, u_1} Hu6 Hu3 Hu8 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X)) (@SheafOfModules.pushforward.{u_1, u_1, u_1, u_1, u_1, u_1} Hu5 Hu2 Hu6 Hu3 Hu7 Hu8 Hu4 (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} Y) (AlgebraicGeometry.Scheme.ringCatSheaf.{u_1} X) (@ArithmeticThetaPolygonCartierR0133.unitPullback._proof_1.{u_1} X Y f) (@AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom.{u_1} X Y f)) := by sorry
run_cmd do
 for i in [1:3] do
  let n := ("ArithmeticThetaPolygonCartierR0133.unitPullback._proof_" ++ toString i).toName
  let ci ← Lean.getConstInfo n
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
def unitPullback {X Y: Scheme.{u}} (f: X ⟶ Y): (Scheme.Modules.pullback f).obj (z8.unit Y.ringCatSheaf: Y.Modules) ⟶ (z8.unit X.ringCatSheaf: X.Modules):= z8.pullbackObjUnitToUnit f.toRingCatSheafHom ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 ru1295 nu1295 universe u namespace ArithmeticThetaPolygonCartierR0133 namespace GlobalCartierIdealLineR0133 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 def quotientMap {X: Scheme.{u}} (I: X.IdealSheafData): (z8.unit X.ringCatSheaf: X.Modules) ⟶ (Scheme.Modules.pushforward I.subschemeι).obj (z8.unit I.subscheme.ringCatSheaf):= z8.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom def idealModule {X: Scheme.{u}} (I: X.IdealSheafData): X.Modules:= kernel (quotientMap I) ec979 1 ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaPolygonCartierR0133  ec979 1 section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaProjectiveEffectivityR0135 open CategoryTheory AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaPositiveLineR0134 attribute [local instance] z6.gradedAlgebra variable (k: Type u) [z1 k] [z2 k] structure Model {r: ℕ} {hr: 0 < r} (T: Tower k r hr) where (X: Scheme.{u}) (p: X ⟶ Spec (z9.of (z4 k))) (inclusion: ∀ n, (T.atlas n).X ⟶ X)
def genericBase: Spec (z9.of (z5 k)) ⟶ Spec (z9.of (z4 k)):= Spec.map (z9.ofHom (algebraMap (z4 k) (z5 k))) def genericStructure {r: ℕ} {hr: 0 < r} {T: Tower k r hr} (M: Model k T):= CategoryTheory.Limits.pullback.snd M.p (genericBase k) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaAlgebraizedMarkedLineR0136 open CategoryTheory AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaPolygonCohomologyR0131 open ArithmeticThetaPolygonCartierR0133 variable (k: Type u) [z1 k] [z2 k] def baseScheme: Scheme.{u}:= Spec (z9.of (z4 k)) ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136 namespace AlgebraizedMarkedIdealSpecializationR0136 ec979 1 ec979 1 namespace AlgebraicGeometry namespace OModulePresheaf ec979 1 ec979 1 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136.CoherentCompletion namespace HomCompleteAux   ec979 1 ec979 3 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2
namespace ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 2 namespace ArithmeticThetaScaledAnnularR0050 ec979 1      section rc590 eu1295 au1295 nu1295 universe u namespace ArithmeticThetaIdentitySectionsR0138 open CategoryTheory AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaPolygonCartierR0133 open ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaAlgebraizedMarkedLineR0136 variable (k: Type u) [z1 k] [z2 k] def powerModule {r: ℕ} {hr: 0 < r} {T: Tower k r hr} (M: Model k T) (s: baseScheme k ⟶ M.X) (d: ℕ): M.X.Modules:= GlobalCartierIdealLineR0133.idealModule (s.ker^d) ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaIdentitySectionsR0138  ec979 1 section rc590 eu1295 au1295 ru1295 nu1295 universe u namespace ArithmeticThetaGenericEvaluationR0140 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaPolygonCartierR0133 open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaAlgebraizedMarkedLineR0136 open ArithmeticThetaIdentitySectionsR0138
variable (k: Type u) [z1 k] [z2 k] variable {r: ℕ} {hr: 0 < r} {T: Tower k r hr} def genericScheme (M: Model k T): Scheme.{u}:= pullback M.p (genericBase k) def genericInclusion (M: Model k T): genericScheme k M ⟶ M.X:= pullback.fst M.p (genericBase k) def genericPower (M: Model k T) (s: baseScheme k ⟶ M.X) (d: ℕ): (genericScheme k M).Modules:= (Scheme.Modules.pullback (genericInclusion k M)).obj (powerModule k M s d) def GenericDual (M: Model k T) (s: baseScheme k ⟶ M.X) (d: ℕ):= genericPower k M s d ⟶ (z8.unit (genericScheme k M).ringCatSheaf: (genericScheme k M).Modules) def scalarAt (M: Model k T) (U: (genericScheme k M).Opens) (c: z5 k): (genericScheme k M).presheaf.obj (Opposite.op U):= (genericScheme k M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ((genericStructure k M).appTop ((Scheme.ΓSpecIso (z9.of (z5 k))).inv c)) ec979 1 ec979 1 ec979 1 ec979 1 section rc590 eu1295 set_option maxHeartbeats 1600000 set_option linter.style.haveILetI false au1295 ru1295 nu1295 universe u namespace ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open scoped TensorProduct open MonoidalCategory open ArithmeticThetaPolygonCartierR0133 (unitPullback)
def dualComparison {X Y: Scheme.{u}} (c: X ⟶ Y) (L: Y.Modules): (Scheme.Modules.pullback c).obj (Scheme.Modules.dual L) ⟶ Scheme.Modules.dual ((Scheme.Modules.pullback c).obj L):= MonoidalClosed.curry ((Scheme.Modules.pullbackTensorObjIso c L (Scheme.Modules.dual L)).inv ≫ (Scheme.Modules.pullback c).map ((ihom.ev L).app (𝟙_ Y.Modules)) ≫ unitPullback c) lemma dualComparison_isIso {X Y: Scheme.{u}} (c: X ⟶ Y) (L: Y.Modules) (hL: Scheme.Modules.IsInvertible L): IsIso (dualComparison c L):= by sorry ec979 2 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaModelSymmetriesR0137 ec979 1 section rc590 eu1295 au1295 ru1295 nu1295 universe u namespace ArithmeticThetaGeometricLiftsR0141 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 open ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaAlgebraizedMarkedLineR0136 open ArithmeticThetaIdentitySectionsR0138 open ArithmeticThetaGenericEvaluationR0140 open ArithmeticThetaModelSymmetriesR0137 variable (k: Type u) [z1 k] [z2 k] variable {r: ℕ} {hr: 0 < r} {T: Tower k r hr} def Lift (M: Model k T) (s: baseScheme k ⟶ M.X) (d: ℕ) (f: genericScheme k M ⟶ genericScheme k M):= genericPower k M s d ≅ (Scheme.Modules.pullback f).obj (genericPower k M s d)
def act (M: Model k T) (s: baseScheme k ⟶ M.X) (d: ℕ) (f: genericScheme k M ⟶ genericScheme k M) (e: Lift k M s d f) (φ: GenericDual k M s d): GenericDual k M s d:= e.hom ≫ (Scheme.Modules.pullback f).map φ ≫ ArithmeticThetaPolygonCartierR0133.unitPullback f ec979 1 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaCubicModelR0144 ec979 1 namespace ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144 ec979 2  namespace ArithmeticThetaCompactifiedDifferentialR0145 ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145  ec979 1 namespace ArithmeticThetaCompactifiedDifferentialR0145  ec979 1 namespace ArithmeticThetaGeneralEllipticKatoR0168  ec979 1  namespace GoodReductionJacobian  ec979 1          namespace ArithmeticThetaSchemeLevelR0204
ec979 1 namespace ArithmeticThetaSchemeLevelR0204  ec979 1 namespace ArithmeticThetaSchemeLevelR0204  ec979 1 namespace ArithmeticThetaSchemeHodgeR0205 ec979 1 namespace ArithmeticThetaSchemeHodgeR0205  ec979 1   namespace ArithmeticThetaTateCuspsR0181 ec979 1  namespace ArithmeticThetaSchemeHodgeR0205  ec979 1  namespace ArithmeticThetaComponentDegreeR0184 ec979 1 namespace ArithmeticThetaComponentDegreeR0184  ec979 1  namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaGeometricLiftsR0141 ec979 1 namespace ArithmeticThetaSharpCoverR0194 ec979 1 namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso namespace AlgebraicGeometry namespace Scheme namespace Modules namespace P2K2 ec979 4 ec979 1 ec979 1 section rc590 eu1295 au1295 ru1295 set_option backward.isDefEq.respectTransparency.types false set_option maxHeartbeats 1600000 set_option maxRecDepth 4096 set_option linter.style.haveILetI false nu1295
namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194 namespace ArithmeticFamily ec979 1 ec979 2 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
def dualLift {Y : Scheme} (f : Y ⟶ Y) (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) (α : (Scheme.Modules.pullback f).obj M ≅ M) : (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M) ≅ Scheme.Modules.dual M := by
  letI := dualComparison_isIso f M hM
  exact asIso (dualComparison f M) ≪≫
    ((MonoidalClosed.internalHom (C := Y.Modules)).mapIso α.symm.op).app (𝟙_ Y.Modules)
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaTateCuspsR0181 open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144 open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136 open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136 ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily ec979 3 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta ec979 4 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta  ec979 4 ec979 1 ec979 1 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244 ec979 1 namespace ArithmeticThetaSchemeDiscriminantR0244  ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259 ec979 1 namespace ArithmeticThetaSchemeThetaMarkingR0259  ec979 1 
  namespace ArithmeticThetaInvariantRatiosR0265  ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266  ec979 1 namespace ArithmeticThetaGlobalProjectiveRatiosR0266 ec979 1 eu1295 nu1295 open CategoryTheory AlgebraicGeometry eu1295 au1295 ru1295 nu1295 universe u open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 open ArithmeticThetaGenericEvaluationR0140 namespace ArithmeticThetaGenericEvaluationR0140 variable (k : Type u) [Field k] [CharZero k] variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def Combines (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (c : Fin m → LaurentSeries k)
    (φ : GenericDual k M s d) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)),
    φ.app U x = ∑ ν : Fin m, scalarAt k M U (c ν) * (show (genericScheme k M).presheaf.obj (Opposite.op U) from (b ν).app U x)
end ArithmeticThetaGenericEvaluationR0140 namespace ArithmeticThetaGeometricLiftsR0141 variable (k : Type u) [Field k] [CharZero k] variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def HasBasis (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) : Prop :=
  ∀ φ : GenericDual k M s d, ∃! c : Fin m → LaurentSeries k,
    Combines k M s d m b c φ
end ArithmeticThetaGeometricLiftsR0141 namespace ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction universe u_1 variable {X : Scheme.{u_1}}
def globalAct (f : X ⟶ X) {M : X.Modules}
    (α : (Scheme.Modules.pullback f).obj M ≅ M) (s : Γ(M, ⊤)) : Γ(M, ⊤) :=
  α.hom.app ⊤ (Scheme.Modules.pullbackLocalSection f s)
end ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction end end eu1295 au1295 ru1295 set_option backward.isDefEq.respectTransparency.types false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false nu1295 universe u open CategoryTheory MonoidalCategory Limits Opposite namespace SheafOfModules open PresheafOfModules PresheafOfModules.InternalHom Functor.Monoidal Functor.LaxMonoidal Functor.OplaxMonoidal
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))
abbrev ihomModel : PMod 𝒪 :=
  PresheafOfModules.ihomObj ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N)
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
def ihomModelToIhom : ihomModel 𝒪 h𝒪 M N ⟶ (toPMod 𝒪 h𝒪).obj ((ihom M).obj N) :=
  (sheafifyAdj 𝒪 h𝒪).unit.app (ihomModel 𝒪 h𝒪 M N)
instance isIso_ihomModelToIhom : IsIso (ihomModelToIhom 𝒪 h𝒪 M N) := by sorry
def ihomModelSectionsIso (X : Cᵒᵖ) :
    (ihomModel 𝒪 h𝒪 M N).obj X ≅ ((toPMod 𝒪 h𝒪).obj ((ihom M).obj N)).obj X :=
  (PresheafOfModules.evaluation _ X).mapIso (asIso (ihomModelToIhom 𝒪 h𝒪 M N))
def ihomSectionsEquivFamily (X : Cᵒᵖ) :
    ((ihom M).obj N).val.obj X ≃+ naturalFamilies ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N) X :=
  ((ihomModelSectionsIso 𝒪 h𝒪 M N X).toLinearEquiv.toAddEquiv).symm
end SheafOfModules namespace AlgebraicGeometry.Scheme.Modules open TopologicalSpace variable {X : Scheme.{u}}
variable (X) in
abbrev toPMod : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property
variable (M N : X.Modules)
def homOfFamily (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤)) :
    M ⟶ N :=
  ⟨{ app := fun V => ModuleCat.ofHom
        { toFun := fun x => φ.1 (homOfLE le_top).op x
          map_add' := fun x y => (φ.1 _).map_add x y
          map_smul' := fun r x => (φ.1 (homOfLE le_top).op).map_smul r x }
     naturality := fun {V V'} i => by
       ext x
       change φ.1 (homOfLE le_top).op (M.val.map i x) = N.val.map i (φ.1 (homOfLE le_top).op x)
       erw [φ.2 (homOfLE le_top).op i x]
       exact PresheafOfModules.InternalHom.congr_app φ (Subsingleton.elim _ _) _ }⟩
@[simp] lemma homOfFamily_app_apply
    (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤))
    (V : X.Opens) (x : Γ(M, V)) : (homOfFamily M N φ).app V x = φ.1 (homOfLE le_top).op x := rfl
def familyOfHom (ψ : M ⟶ N) :
    PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤) :=
  ⟨fun V _ =>
    { toFun := fun x => ψ.val.app V x
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => (ψ.val.app V).hom.map_smul r x },
    fun _ _ _ g x => (PresheafOfModules.naturality_apply ψ.val g x).symm⟩
@[simp] lemma familyOfHom_app (ψ : M ⟶ N) {V : (X.Opens)ᵒᵖ} (f : Opposite.op ⊤ ⟶ V)
    (x : Γ(M, V.unop)) : (familyOfHom M N ψ).1 f x = ψ.app V.unop x := rfl
def homEquivFamily :
    (M ⟶ N) ≃+ PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M)
      ((toPMod X).obj N) (Opposite.op ⊤) where
  toFun := familyOfHom M N
  invFun := homOfFamily M N
  left_inv ψ := by ext V x; rfl
  right_inv φ := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    exact PresheafOfModules.InternalHom.congr_app φ (Subsingleton.elim _ _) _
  map_add' ψ ψ' := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    rfl
set_option hygiene false set_option quotPrecheck false local notation "IH1278x0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X)))) local notation "IH1278x1" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} IH1278x0) (TopCat.str.{u_1} IH1278x0)) set_option quotPrecheck true set_option hygiene true
theorem _root_.AlgebraicGeometry.Scheme.Modules.ihomEval._proof_1.{u_1} : ∀ {X : AlgebraicGeometry.Scheme.{u_1}}, @CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.{u_1, u_1, u_1, u_1 + 1, u_1, u_1} IH1278x1 (@Preorder.smallCategory.{u_1} IH1278x1 (@PartialOrder.toPreorder.{u_1} IH1278x1 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} IH1278x0) (TopCat.str.{u_1} IH1278x0)))) (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} IH1278x0) (TopCat.str.{u_1} IH1278x0)) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory.{u_1} (fun (x1 x2 : AddCommGrpCat.{u_1}) => @AddMonoidHom.{u_1, u_1} (AddCommGrpCat.carrier.{u_1} x1) (AddCommGrpCat.carrier.{u_1} x2) (@AddZeroClass.toAddZero.{u_1} (AddCommGrpCat.carrier.{u_1} x1) (@AddMonoid.toAddZeroClass.{u_1} (AddCommGrpCat.carrier.{u_1} x1) (@SubNegMonoid.toAddMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} x1) (@AddGroup.toSubNegMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} x1) (@AddCommGroup.toAddGroup.{u_1} (AddCommGrpCat.carrier.{u_1} x1) (AddCommGrpCat.str.{u_1} x1)))))) (@AddZeroClass.toAddZero.{u_1} (AddCommGrpCat.carrier.{u_1} x2) (@AddMonoid.toAddZeroClass.{u_1} (AddCommGrpCat.carrier.{u_1} x2) (@SubNegMonoid.toAddMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} x2) (@AddGroup.toSubNegMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} x2) (@AddCommGroup.toAddGroup.{u_1} (AddCommGrpCat.carrier.{u_1} x2) (AddCommGrpCat.str.{u_1} x2))))))) AddCommGrpCat.carrier.{u_1} (fun (X Y : AddCommGrpCat.{u_1}) => @AddMonoidHom.instFunLike.{u_1, u_1} (AddCommGrpCat.carrier.{u_1} X) (AddCommGrpCat.carrier.{u_1} Y) (@AddZeroClass.toAddZero.{u_1} (AddCommGrpCat.carrier.{u_1} X) (@AddMonoid.toAddZeroClass.{u_1} (AddCommGrpCat.carrier.{u_1} X) (@SubNegMonoid.toAddMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} X) (@AddGroup.toSubNegMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} X) (@AddCommGroup.toAddGroup.{u_1} (AddCommGrpCat.carrier.{u_1} X) (AddCommGrpCat.str.{u_1} X)))))) (@AddZeroClass.toAddZero.{u_1} (AddCommGrpCat.carrier.{u_1} Y) (@AddMonoid.toAddZeroClass.{u_1} (AddCommGrpCat.carrier.{u_1} Y) (@SubNegMonoid.toAddMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} Y) (@AddGroup.toSubNegMonoid.{u_1} (AddCommGrpCat.carrier.{u_1} Y) (@AddCommGroup.toAddGroup.{u_1} (AddCommGrpCat.carrier.{u_1} Y) (AddCommGrpCat.str.{u_1} Y))))))) AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{u_1} := by sorry
run_cmd do
 let n := `AlgebraicGeometry.Scheme.Modules.ihomEval._proof_1
 let ci ← Lean.getConstInfo n
 Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
set_option hygiene false
set_option quotPrecheck false
local notation "IH1293x0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} X))))
local notation "IH1293x1" => (@TopologicalSpace.Opens.{u_1} (TopCat.carrier.{u_1} IH1293x0) (TopCat.str.{u_1} IH1293x0))
set_option quotPrecheck true
set_option hygiene true
theorem _root_.AlgebraicGeometry.Scheme.Modules.ihomEval._proof_2.{u_1} : ∀ {X : AlgebraicGeometry.Scheme.{u_1}}, @CategoryTheory.HasWeakSheafify.{u_1, u_1, u_1, u_1 + 1} IH1293x1 (@Preorder.smallCategory.{u_1} IH1293x1 (@PartialOrder.toPreorder.{u_1} IH1293x1 (@TopologicalSpace.Opens.instPartialOrder.{u_1} (TopCat.carrier.{u_1} IH1293x0) (TopCat.str.{u_1} IH1293x0)))) (@Opens.grothendieckTopology.{u_1} (TopCat.carrier.{u_1} IH1293x0) (TopCat.str.{u_1} IH1293x0)) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory.{u_1} := by sorry
run_cmd do
 let n := `AlgebraicGeometry.Scheme.Modules.ihomEval._proof_2
 let ci ← Lean.getConstInfo n
 Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
def ihomGlobalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
    (Opposite.op ⊤)).trans (homEquivFamily M N).symm
end AlgebraicGeometry.Scheme.Modules end end set_option hygiene false set_option quotPrecheck false local notation "GD1259x3" => (@ArithmeticThetaGenericEvaluationR0140.genericScheme.{0} k inst inst_1 r hr T M) local notation "GD1259x0" => (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0} CommRingCat.instCategory.{0} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0} CommRingCat.instCategory.{0} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} GD1259x3)))) local notation "GD1259x25" => (@TopologicalSpace.Opens.instCompleteLattice.{0} (TopCat.carrier.{0} GD1259x0) (TopCat.str.{0} GD1259x0)) local notation "GD1259x6" => (@TopologicalSpace.Opens.{0} (TopCat.carrier.{0} GD1259x0) (TopCat.str.{0} GD1259x0)) local notation "GD1259x19" => (@Preorder.toLE.{0} GD1259x6 (@PartialOrder.toPreorder.{0} GD1259x6 (@SemilatticeSup.toPartialOrder.{0} GD1259x6 (@Lattice.toSemilatticeSup.{0} GD1259x6 (@CompleteLattice.toLattice.{0} GD1259x6 GD1259x25))))) local notation "GD1259x9" => (@Opposite.op.{1} GD1259x6 (@Top.top.{0} GD1259x6 (@OrderTop.toTop.{0} GD1259x6 GD1259x19 (@BoundedOrder.toOrderTop.{0} GD1259x6 GD1259x19 (@CompleteLattice.toBoundedOrder.{0} GD1259x6 GD1259x25))))) local notation "GD1259x18" => (@Preorder.smallCategory.{0} GD1259x6 (@PartialOrder.toPreorder.{0} GD1259x6 (@TopologicalSpace.Opens.instPartialOrder.{0} (TopCat.carrier.{0} GD1259x0) (TopCat.str.{0} GD1259x0)))) local notation "GD1259x24" => (@CategoryTheory.Category.opposite.{0, 0} GD1259x6 GD1259x18)
local notation "GD1259x10" => (@AlgebraicGeometry.Scheme.Modules.instCategory.{0} GD1259x3) local notation "GD1259x23" => (AlgebraicGeometry.Scheme.Modules.monoidalCategory.{0} GD1259x3) local notation "GD1259x7" => (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x23)) local notation "GD1259x11" => (@ArithmeticThetaGenericEvaluationR0140.genericPower.{0} k inst inst_1 r hr T M s d) local notation "GD1259x14" => (@CategoryTheory.ihom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x23 GD1259x11 (@CategoryTheory.MonoidalClosed.closed.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x23 (AlgebraicGeometry.Scheme.Modules.monoidalClosed.{0} GD1259x3) GD1259x11)) local notation "GD1259x21" => (@CategoryTheory.Functor.obj.{0, 0, 1, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x14 GD1259x7) local notation "GD1259x1" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} GD1259x6) GD1259x24 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} GD1259x3 GD1259x21) GD1259x9) local notation "GD1259x8" => (@SheafOfModules.unit.{0, 0, 0} GD1259x6 GD1259x18 (@Opens.grothendieckTopology.{0} (TopCat.carrier.{0} GD1259x0) (TopCat.str.{0} GD1259x0)) (AlgebraicGeometry.Scheme.ringCatSheaf.{0} GD1259x3))
local notation "GD1259x2" => (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} GD1259x6) GD1259x24 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} GD1259x3 (@CategoryTheory.Functor.obj.{0, 0, 1, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x14 GD1259x8)) GD1259x9) local notation "GD1259x17" => (@CategoryTheory.ReflQuiver.toQuiver.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) (@CategoryTheory.catToReflQuiver.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10)) local notation "GD1259x4" => (@Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x17 GD1259x11 GD1259x8) local notation "GD1259x5" => (@Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x17 GD1259x11 GD1259x7) local notation "GD1259x22" => (@CategoryTheory.Abelian.toPreadditive.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (@AlgebraicGeometry.Scheme.Modules.instAbelian.{0} GD1259x3)) local notation "GD1259x12" => (@AddCommMagma.toAdd.{0} GD1259x5 (@AddCommSemigroup.toAddCommMagma.{0} GD1259x5 (@AddCommMonoid.toAddCommSemigroup.{0} GD1259x5 (@AddCommGroup.toAddCommMonoid.{0} GD1259x5 (@CategoryTheory.Preadditive.homGroup.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x22 GD1259x11 GD1259x7)))))
local notation "GD1259x13" => (@AddCommMagma.toAdd.{0} GD1259x4 (@AddCommSemigroup.toAddCommMagma.{0} GD1259x4 (@AddCommMonoid.toAddCommSemigroup.{0} GD1259x4 (@AddCommGroup.toAddCommMonoid.{0} GD1259x4 (@CategoryTheory.Preadditive.homGroup.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x22 GD1259x11 GD1259x8))))) local notation "GD1259x15" => (@AddCommMagma.toAdd.{0} (AddCommGrpCat.carrier.{0} GD1259x1) (@AddCommSemigroup.toAddCommMagma.{0} (AddCommGrpCat.carrier.{0} GD1259x1) (@AddCommMonoid.toAddCommSemigroup.{0} (AddCommGrpCat.carrier.{0} GD1259x1) (@AddCommGroup.toAddCommMonoid.{0} (AddCommGrpCat.carrier.{0} GD1259x1) (AddCommGrpCat.str.{0} GD1259x1))))) local notation "GD1259x16" => (@AddCommMagma.toAdd.{0} (AddCommGrpCat.carrier.{0} GD1259x2) (@AddCommSemigroup.toAddCommMagma.{0} (AddCommGrpCat.carrier.{0} GD1259x2) (@AddCommMonoid.toAddCommSemigroup.{0} (AddCommGrpCat.carrier.{0} GD1259x2) (@AddCommGroup.toAddCommMonoid.{0} (AddCommGrpCat.carrier.{0} GD1259x2) (AddCommGrpCat.str.{0} GD1259x2))))) local notation "GD1259x20" => (@CategoryTheory.ReflQuiver.toQuiver.{0, 1} AlgebraicGeometry.Scheme.{0} (@CategoryTheory.catToReflQuiver.{0, 1} AlgebraicGeometry.Scheme.{0} AlgebraicGeometry.Scheme.instCategory.{0})) set_option quotPrecheck true set_option hygiene true
theorem _root_.ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.genericDual_globalAct : ∀ (k : Type) [inst : Field.{0} k] [inst_1 : @CharZero.{0} k (@AddGroupWithOne.toAddMonoidWithOne.{0} k (@Ring.toAddGroupWithOne.{0} k (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst))))] {r : Nat} {hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r} {T : @ArithmeticThetaInfinitesimalPolygonR0129.Tower.{0} k inst inst_1 r hr} (M : @ArithmeticThetaProjectiveEffectivityR0135.Model.{0} k inst inst_1 r hr T) (s : @Quiver.Hom.{0, 1} AlgebraicGeometry.Scheme.{0} GD1259x20 (@ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme.{0} k inst) (@ArithmeticThetaProjectiveEffectivityR0135.Model.X.{0} k inst inst_1 r hr T M)) (d : Nat) (hL : @AlgebraicGeometry.Scheme.Modules.IsInvertible.{0} GD1259x3 GD1259x11) (f : @Quiver.Hom.{0, 1} AlgebraicGeometry.Scheme.{0} GD1259x20 GD1259x3 GD1259x3) (e : @ArithmeticThetaGeometricLiftsR0141.Lift.{0} k inst inst_1 r hr T M s d f) (v : AddCommGrpCat.carrier.{0} (@CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} GD1259x6) GD1259x24 Ab.{0} AddCommGrpCat.instCategory.{0} (@AlgebraicGeometry.Scheme.Modules.presheaf.{0} GD1259x3 (@AlgebraicGeometry.Scheme.Modules.dual.{0} GD1259x3 GD1259x11)) GD1259x9)), @Eq.{1} GD1259x5 (@DFunLike.coe.{1, 1, 1} (@AddEquiv.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x1) GD1259x5 GD1259x15 GD1259x12) (AddCommGrpCat.carrier.{0} GD1259x1) (fun (x : AddCommGrpCat.carrier.{0} GD1259x1) => @Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x17 GD1259x11 GD1259x7) (@EquivLike.toFunLike.{1, 1, 1} (@AddEquiv.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x1) GD1259x5 GD1259x15 GD1259x12) (AddCommGrpCat.carrier.{0} GD1259x1) GD1259x5 (@AddEquiv.instEquivLike.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x1) GD1259x5 GD1259x15 GD1259x12)) (@AlgebraicGeometry.Scheme.Modules.ihomGlobalSectionsEquiv.{0} GD1259x3 GD1259x11 GD1259x7) (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.SectionAction.globalAct.{0} GD1259x3 f GD1259x21 (@ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily.LocalTheta.dualLift.{0} GD1259x3 f GD1259x11 hL (@CategoryTheory.Iso.symm.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 GD1259x11 (@CategoryTheory.Functor.obj.{0, 0, 1, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x10 (@AlgebraicGeometry.Scheme.Modules.pullback.{0} GD1259x3 GD1259x3 f) GD1259x11) e)) v)) (@ArithmeticThetaGeometricLiftsR0141.act.{0} k inst inst_1 r hr T M s d f e (@DFunLike.coe.{1, 1, 1} (@AddEquiv.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x2) GD1259x4 GD1259x16 GD1259x13) (AddCommGrpCat.carrier.{0} GD1259x2) (fun (x : AddCommGrpCat.carrier.{0} GD1259x2) => @Quiver.Hom.{0, 1} (AlgebraicGeometry.Scheme.Modules.{0} GD1259x3) GD1259x17 GD1259x11 GD1259x8) (@EquivLike.toFunLike.{1, 1, 1} (@AddEquiv.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x2) GD1259x4 GD1259x16 GD1259x13) (AddCommGrpCat.carrier.{0} GD1259x2) GD1259x4 (@AddEquiv.instEquivLike.{0, 0} (AddCommGrpCat.carrier.{0} GD1259x2) GD1259x4 GD1259x16 GD1259x13)) (@AlgebraicGeometry.Scheme.Modules.ihomGlobalSectionsEquiv.{0} GD1259x3 GD1259x11 GD1259x8) v)) := by sorry
end
