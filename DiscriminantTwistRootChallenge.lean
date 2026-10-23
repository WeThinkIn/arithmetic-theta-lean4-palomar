module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
macro "rC":command =>`(run_cmd Lean.modifyEnv fun env =>Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {})
elab "eN" n:num : command => do let ss ← Lean.Elab.Command.getScopes; let ns := (ss.take n.getNat).reverse.foldl (fun a s => Lean.Name.str a s.header) Lean.Name.anonymous; Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent ns)))
noncomputable section
universe u v
set_option hygiene false
set_option quotPrecheck false
local notation"p0(" X ")" =>(@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) local notation"p2" =>(Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) local notation"p7" =>(@Finsupp p2 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) local notation"p8(" R "," inst ")" =>(@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) local notation"p20(" R "," inst ")" =>(@AddMonoidAlgebra.instAddCommMonoid R p7 p8(R,inst)) local notation"p17(" R "," inst ")" =>(@AddMonoidAlgebra.instModule R R p7 p8(R,inst) p8(R,inst) (@Semiring.toModule R p8(R,inst))) local notation"p5(" R "," inst ")" =>(@MvPolynomial p2 R (@CommRing.toCommSemiring R inst)) local notation"p28(" R "," inst ")" =>(@Submodule R p5(R,inst) p8(R,inst) p20(R,inst) p17(R,inst)) local notation"p11" =>(@Finsupp.instAddMonoid p2 Nat Nat.instAddMonoid) local notation"p22(" R "," inst ")" =>(@AddMonoidAlgebra.semiring R p7 p8(R,inst) p11) local notation"p24(" R "," inst ")" =>(@Submodule.setLike R p5(R,inst) p8(R,inst) p20(R,inst) p17(R,inst)) local notation"p1(" R "," W "," inst ")" =>(@HomogeneousIdeal.toIdeal Nat p28(R,inst) p5(R,inst) p22(R,inst) p24(R,inst) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1 R inst) (@MvPolynomial.homogeneousSubmodule p2 R (@CommRing.toCommSemiring R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra p2 R (@CommRing.toCommSemiring R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR R inst (@WeierstrassCurve.toProjective R W))) local notation"p9(" X ")" =>(@TopologicalSpace.Opens (TopCat.carrier p0(X)) (TopCat.str p0(X))) local notation"p6(" X ")" =>(@Preorder.smallCategory p9(X) (@PartialOrder.toPreorder p9(X) (@TopologicalSpace.Opens.instPartialOrder (TopCat.carrier p0(X)) (TopCat.str p0(X))))) local notation"p13(" X ")" =>(@CategoryTheory.Functor (Opposite p9(X)) (@CategoryTheory.Category.opposite p9(X) p6(X)) RingCat RingCat.instCategory) local notation"p18(" X ")" =>(@CategoryTheory.Functor.category (Opposite p9(X)) (@CategoryTheory.Category.opposite p9(X) p6(X)) RingCat RingCat.instCategory) local notation"p19(" X ")" =>(@Opens.grothendieckTopology (TopCat.carrier p0(X)) (TopCat.str p0(X))) local notation"p3(" X ")" =>(@CategoryTheory.ObjectProperty.FullSubcategory.obj p13(X) p18(X) (@CategoryTheory.Presheaf.IsSheaf p9(X) p6(X) RingCat RingCat.instCategory p19(X)) (AlgebraicGeometry.Scheme.ringCatSheaf X)) local notation"p16(" R "," inst ")" =>(@Algebra.toSMul R p5(R,inst) (@CommRing.toCommSemiring R inst) p22(R,inst) (@AddMonoidAlgebra.algebra R R p7 (@CommRing.toCommSemiring R inst) p8(R,inst) (@Algebra.id R (@CommRing.toCommSemiring R inst)) p11)) local notation"p32(" R "," inst ")" =>(@AddMonoidAlgebra.ring R p7 (@CommRing.toRing R inst) p11) local notation"p4(" R "," W "," inst ")" =>(@Submodule.Quotient.module' p5(R,inst) p5(R,inst) p32(R,inst) (@AddMonoidAlgebra.addCommGroup R p7 (@CommRing.toRing R inst)) (@Semiring.toModule p5(R,inst) p22(R,inst)) R p8(R,inst) p16(R,inst) (@MvPolynomial.instModuleSelf p2 R inst) (@WeierstrassProjModel.kw_lrComul_tensorProj._proof_1 R inst) p1(R,W,inst)) local notation"p21(" R "," inst ")" =>(@AddMonoidAlgebra.commRing R p7 inst (@Finsupp.instAddCommMonoid p2 Nat Nat.instAddCommMonoid)) local notation"p10(" R "," W "," inst ")" =>(@Submodule.Quotient.addCommGroup p5(R,inst) p5(R,inst) (@CommRing.toRing p5(R,inst) p21(R,inst)) (@Ring.toAddCommGroup p5(R,inst) (@CommRing.toRing p5(R,inst) p21(R,inst))) (@Semiring.toModule p5(R,inst) (@Ring.toSemiring p5(R,inst) (@CommRing.toRing p5(R,inst) p21(R,inst)))) p1(R,W,inst)) local notation"p12(" R "," W "," inst ")" =>(@WeierstrassProjModel.ProjModelRingCR R inst (@WeierstrassCurve.toProjective R W)) local notation"p14(" R "," W "," inst ")" =>(@Submodule.Quotient.addCommGroup p5(R,inst) p5(R,inst) p32(R,inst) (@AddMonoidAlgebra.addCommGroup R p7 (@CommRing.toRing R inst)) (@Semiring.toModule p5(R,inst) p22(R,inst)) p1(R,W,inst)) local notation"p15(" R "," inst ")" =>(@Ring.toSemiring p5(R,inst) p32(R,inst)) local notation"p23(" R "," inst ")" =>(@OfNat.ofNat R (nat_lit 0) (@Zero.toOfNat0 R (@MulZeroClass.toZero R (@instMulZeroClassOfSemiring R p8(R,inst))))) local notation"p25(" X ")" =>(@CategoryTheory.CategoryStruct.id p13(X) (@CategoryTheory.Category.toCategoryStruct p13(X) p18(X)) p3(X)) local notation"p26" =>(@Semiring.toNonAssocSemiring (RingCat.carrier S) (@Ring.toSemiring (RingCat.carrier S) (RingCat.ring S))) local notation"p27" =>(@Semiring.toNonAssocSemiring (RingCat.carrier Y) (@Ring.toSemiring (RingCat.carrier Y) (RingCat.ring Y))) local notation"p29(" R ")" =>(@Semiring.toNonAssocSemiring (RingCat.carrier R) (@Ring.toSemiring (RingCat.carrier R) (RingCat.ring R))) local notation"p30(" X ")" =>(@Semiring.toNonAssocSemiring (RingCat.carrier X) (@Ring.toSemiring (RingCat.carrier X) (RingCat.ring X))) local notation"p31(" R "," W "," inst ")" =>(AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace (@ArithmeticThetaRelativeKatoR0169.Curve R inst W)))
set_option quotPrecheck true
set_option hygiene true
set_option hygiene false
set_option quotPrecheck false
local notation"q0" =>Scheme.Modules.pullback local notation"q1" =>Scheme.{u} local notation"q2" =>CommRingCat.of local notation"q3" =>AddCommGrpCat.carrier.{u_1} local notation"q4" =>Ideal.Quotient.mk local notation"q5" =>CommRingCat.ofHom local notation"q6" =>PresheafOfModules.sheafificationAdjunction local notation"q7" =>Scheme.Modules.pullbackComp local notation"q9" =>WeierstrassCurve.Projective local notation"q10" =>Scheme.Modules.pullbackLocalSection  local notation"q12" =>RingCat.carrier.{u_1} local notation"q13" =>PresheafOfModules.sheafification  local notation"q15" =>Spec.map local notation"q21" =>ArithmeticThetaLegendreAtlasR0176.LegendreAtlas local notation"q22" =>Scheme.Modules.pullbackPushforwardAdjunction local notation"q24" =>SheafOfModules.unit  local notation"q26" =>ArithmeticThetaCompactUnaryR0183.level    local notation"q30" =>Opposite.op local notation"q35" =>ArithmeticThetaPalomarHalf505.powerComparison  local notation"q37" =>ArithmeticThetaGeometricNormR0150.IsFieldMap local notation"q38" =>AlgebraicGeometry.Scheme.{u_1} local notation"q39" =>ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection local notation"q42" =>WeierstrassCurve.{u_1}   local notation"q45" =>SheafOfModules.{u}  local notation"q47" =>PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' local notation"q48" =>SheafOfModules.unitToPushforwardObjUnit local notation"q49" =>GoodReductionJacobian.schemeHomOverComp   local notation"q52" =>Scheme.Modules.pushforward local notation"q53" =>CommRing.{u_1} local notation"q56" =>WeierstrassProjModel.projModelStrCR local notation"q57" =>ArithmeticThetaOpenHodgeR0180.power local notation"q58" =>H.line   local notation"q61" =>MvPolynomial.homogeneousSubmodule local notation"q65" =>AddCommGrpCat.str.{u_1} local notation"q66" =>WeierstrassProjModel.projModelCR local notation"q67" =>ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison local notation"q72" =>ArithmeticThetaTateSeries.tateX  local notation"q74" =>Polynomial.X  local notation"q76" =>CommRingCat.instCategory.{u_1}  local notation"q78" =>SetLike.GradedMonoid local notation"q79" =>ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient local notation"q80" =>ArithmeticThetaCompactifiedDifferentialR0145.relativeD local notation"q81" =>RingCat.{u_1}  local notation"q83" =>Set.range local notation"q84" =>ArithmeticThetaCompatibleLevelR0178.CompatibleCover local notation"q85" =>AddCommGrpCat.{u_1}
set_option hygiene true
set_option quotPrecheck true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace NeronModelInfra
rC abbrev SchemeHomOver {B Y X:q1} (g:Y ⟶ B) (f:X ⟶ B):={φ:Y ⟶ X // φ ≫ f = g}
eN 1 namespace HomogeneousIdealQuotientGrading
rC open DirectSum
section Engine
variable {ι A σ τ:Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜:ι → σ)
variable (I:Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ:ι → τ)
def pieceHom (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (i:ι):𝒜 i →+ ℬ i:=AddMonoidHom.codRestrict ((q4 I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i) (fun a =>hmem i a a.2)
@[simp] lemma pieceHom_coe (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (i:ι) (a:𝒜 i):(pieceHom 𝒜 I ℬ hmem i a:A ⧸ I) = q4 I (a:A):=by sorry
omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in
theorem gradedMonoidOfImages [AddMonoid ι] [q78 𝒜] (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hsurj:∀ (i:ι),∀ b ∈ ℬ i,∃ a ∈ 𝒜 i,q4 I a = b):q78 ℬ:=by sorry
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (y:⨁ i,𝒜 i):DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y) = q4 I (DirectSum.coeAddMonoidHom 𝒜 y):=by sorry
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i):A →+ ⨁ i,ℬ i:=(DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_of_mem (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) {i:ι} {a:A} (ha:a ∈ 𝒜 i):preDecompose 𝒜 I ℬ hmem a = DirectSum.of (fun j =>ℬ j) i ⟨q4 I a,hmem i a ha⟩:=by sorry
lemma coeAddMonoidHom_preDecompose (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (a:A):DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = q4 I a:=by sorry
lemma preDecompose_eq_zero_of_mem (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hI:I.IsHomogeneous 𝒜) {a:A} (ha:a ∈ I):preDecompose 𝒜 I ℬ hmem a = 0:=by sorry
def quotDecompose (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hI:I.IsHomogeneous 𝒜):A ⧸ I →+ ⨁ i,ℬ i:=QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem) (fun _ ha =>preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
@[simp] lemma quotDecompose_mk (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hI:I.IsHomogeneous 𝒜) (a:A):quotDecompose 𝒜 I ℬ hmem hI (q4 I a) = preDecompose 𝒜 I ℬ hmem a:=by sorry
@[reducible] def decompositionOfImages (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hsurj:∀ (i:ι),∀ b ∈ ℬ i,∃ a ∈ 𝒜 i,q4 I a = b) (hI:I.IsHomogeneous 𝒜):DirectSum.Decomposition ℬ :=
  DirectSum.Decomposition.ofAddHom ℬ (quotDecompose 𝒜 I ℬ hmem hI)
    (by
      refine AddMonoidHom.ext fun x =>?_
      obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
      rw [AddMonoidHom.comp_apply,AddMonoidHom.id_apply,quotDecompose_mk,
        coeAddMonoidHom_preDecompose])
    (by
      refine DirectSum.addHom_ext fun i b =>?_
      rw [AddMonoidHom.comp_apply,AddMonoidHom.id_apply,DirectSum.coeAddMonoidHom_of]
      obtain ⟨a,ha,hab⟩:=hsurj i (b:A ⧸ I) b.2
      rw [← hab,quotDecompose_mk,preDecompose_of_mem 𝒜 I ℬ hmem ha]
      exact congrArg _ (Subtype.ext hab))
@[reducible] def gradedRingOfImages (hmem:∀ (i:ι) (a:A),a ∈ 𝒜 i → q4 I a ∈ ℬ i) (hsurj:∀ (i:ι),∀ b ∈ ℬ i,∃ a ∈ 𝒜 i,q4 I a = b) (hI:I.IsHomogeneous 𝒜):GradedRing ℬ where
  toGradedMonoid:=gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition:=decompositionOfImages 𝒜 I ℬ hmem hsurj hI
eN 1 section SubmoduleVersion
variable {ι R A:Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜:ι → Submodule R A)
variable (I:Ideal A)
def quotGradingSubmodule (i:ι):Submodule R (A ⧸ I):=(𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff {i:ι} {x:A ⧸ I}:x ∈ quotGradingSubmodule 𝒜 I i ↔ ∃ a ∈ 𝒜 i,q4 I a = x:=by sorry
lemma mk_mem_quotGradingSubmodule {i:ι} {a:A} (ha:a ∈ 𝒜 i):q4 I a ∈ quotGradingSubmodule 𝒜 I i:=(mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a,ha,rfl⟩
instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [q78 𝒜]:q78 (quotGradingSubmodule 𝒜 I):=by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra (hI:I.IsHomogeneous 𝒜):GradedAlgebra (quotGradingSubmodule 𝒜 I):=gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I) (fun _ _ ha =>mk_mem_quotGradingSubmodule 𝒜 I ha) (fun _ _ hb =>(mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J:HomogeneousIdeal 𝒜):GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal):=quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
eN 1 eN 1 namespace ProjWeierstrassCubicPrime
rC open MvPolynomial
variable {F:Type*} [CommRing F]
theorem isHomogeneous_polynomial (V:q9 F):V.polynomial.IsHomogeneous 3:=by sorry
eN 1 namespace WeierstrassProjModel
rC open MvPolynomial HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R:Type*} [CommRing R]
theorem span_polynomial_isHomogeneousCR (V:q9 R):(Ideal.span {V.polynomial}).IsHomogeneous ((homogeneousSubmodule (Fin 3) R)):=by sorry
def projModelHomogeneousIdealCR (V:q9 R):HomogeneousIdeal ((homogeneousSubmodule (Fin 3) R)):=⟨Ideal.span {V.polynomial},span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : q9 R) : (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl
abbrev ProjModelRingCR (V:q9 R):Type _:=MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR (V:q9 R):ℕ → Submodule R (ProjModelRingCR V):=quotGradingSubmodule ((homogeneousSubmodule (Fin 3) R)) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR (V:q9 R):Scheme:=Proj (projModelGradingCR V)
def projModelStrCR (V:q9 R):Proj (projModelGradingCR V) ⟶ Spec (q2 R):=Proj.toSpecZero (projModelGradingCR V) ≫ q15 (q5 (algebraMap R ((projModelGradingCR V) 0)))
eN 1 variable (R:Type u) [CommRing R]
section ZeroSection
variable (W:WeierstrassCurve R)
open MvPolynomial in
theorem kw_mk_X1_mem_one_CR:q4 (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 1:MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1:=mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
theorem kw_lrComul_tensorProj._proof_1.{u_1}:∀ {R:Type u_1} [inst:q53 R],@IsScalarTower.{u_1,u_1,u_1} R p5(R,inst) p5(R,inst) p16(R,inst) (@instSMulOfMul.{u_1} p5(R,inst) (@Distrib.toMul.{u_1} p5(R,inst) (@instDistribOfSemiring.{u_1} p5(R,inst) p22(R,inst)))) p16(R,inst):=by sorry
theorem kw_lrChart_aux._proof_1.{u_1}:∀ {R:Type u_1} [inst:q53 R] (W:q42 R),@AddSubgroupClass.{u_1,u_1} (@Submodule.{u_1,u_1} R p12(R,W,inst) (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst)) (@AddCommGroup.toAddCommMonoid.{u_1} p12(R,W,inst) p14(R,W,inst)) p4(R,W,inst)) p12(R,W,inst) (@AddGroup.toSubNegMonoid.{u_1} p12(R,W,inst) (@AddCommGroup.toAddGroup.{u_1} p12(R,W,inst) p14(R,W,inst))) (@Submodule.setLike.{u_1, u_1} R p12(R,W,inst) (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst)) (@AddCommGroup.toAddCommMonoid.{u_1} p12(R,W,inst) p14(R,W,inst)) p4(R,W,inst)):=by sorry
theorem kw_lrChart_aux._proof_2.{u_1}:∀ {R:Type u_1} [inst:q53 R] (W:q42 R),@AddSubgroupClass.{u_1,u_1} (@Submodule.{u_1,u_1} R p12(R,W,inst) (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst)) (@AddCommGroup.toAddCommMonoid.{u_1} p12(R,W,inst) p10(R,W,inst)) p4(R,W,inst)) p12(R,W,inst) (@AddGroup.toSubNegMonoid.{u_1} p12(R,W,inst) (@AddCommGroup.toAddGroup.{u_1} p12(R,W,inst) p10(R,W,inst))) (@Submodule.setLike.{u_1, u_1} R p12(R,W,inst) (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst)) (@AddCommGroup.toAddCommMonoid.{u_1} p12(R,W,inst) p10(R,W,inst)) p4(R,W,inst)):=by sorry
theorem kw_lrSixU_toE._proof_1:@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (@One.toOfNat1.{0} Nat Nat.instOne)):=by sorry
theorem kw_lrAdd_comulHom._proof_2.{u_1}:∀ {R:Type u_1} [inst:q53 R],@AddSubmonoidClass.{u_1,u_1} p28(R,inst) p5(R,inst) (@AddMonoid.toAddZeroClass.{u_1} p5(R,inst) (@AddCommMonoid.toAddMonoid.{u_1} p5(R,inst) p20(R,inst))) p24(R,inst):=by sorry
theorem kw_lrAdd_comulHom._proof_3.{u_1}:∀ {R:Type u_1} [inst:q53 R] (W:q42 R),@Ideal.IsTwoSided.{u_1} p5(R,inst) (@CommSemiring.toSemiring.{u_1} p5(R,inst) (@CommRing.toCommSemiring.{u_1} p5(R,inst) p21(R,inst))) (@HomogeneousIdeal.toIdeal.{0,u_1,u_1} Nat p28(R,inst) p5(R,inst) p22(R,inst) p24(R,inst) (@WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} R inst) (@MvPolynomial.homogeneousSubmodule.{0,u_1} p2 R (@CommRing.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra.{0,u_1} p2 R (@CommRing.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W))):=by sorry
theorem kw_lrAddNegDiag_negSubstGen._proof_1:@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))):=by sorry
theorem kwYEvalRingHom._proof_2.{u_1}:∀ (R:Type u_1) [inst:q53 R] (W:q42 R) (a:@MvPolynomial.{0,u_1} p2 R (@CommRing.toCommSemiring.{u_1} R inst)) (ha:@Membership.mem.{u_1,u_1} p5(R,inst) (@Ideal.{u_1} p5(R,inst) p15(R,inst)) (@SetLike.instMembership.{u_1,u_1} (@Ideal.{u_1} p5(R,inst) p15(R,inst)) p5(R,inst) (@Submodule.setLike.{u_1, u_1} p5(R,inst) p5(R,inst) p15(R,inst) (@Semiring.toAddCommMonoid.{u_1} p5(R,inst) p15(R,inst)) (@Semiring.toModule.{u_1} p5(R,inst) p15(R,inst)))) p1(R,W,inst) a),@Eq.{u_1 + 1} R (@DFunLike.coe.{u_1 + 1,u_1 + 1,u_1 + 1} (@RingHom.{u_1,u_1} p5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} p5(R,inst) p15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R p8(R,inst))) p5(R,inst) (fun (x:@MvPolynomial.{0,u_1} p2 R (@CommRing.toCommSemiring.{u_1} R inst)) =>R) (@RingHom.instFunLike.{u_1, u_1} p5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} p5(R,inst) p15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R p8(R,inst))) (@MvPolynomial.eval.{u_1,0} R p2 (@CommRing.toCommSemiring.{u_1} R inst) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p23(R,inst) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R (@AddGroupWithOne.toAddMonoidWithOne.{u_1} R (@Ring.toAddGroupWithOne.{u_1} R (@CommRing.toRing.{u_1} R inst)))))) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p23(R,inst) (@Matrix.vecEmpty.{u_1} R))))) a) p23(R,inst):=by sorry
run_cmd do
  for n in [`WeierstrassProjModel.kw_lrComul_tensorProj._proof_1,`WeierstrassProjModel.kw_lrChart_aux._proof_1,`WeierstrassProjModel.kw_lrChart_aux._proof_2,`WeierstrassProjModel.kw_lrSixU_toE._proof_1,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_2,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_3,`WeierstrassProjModel.kw_lrAddNegDiag_negSubstGen._proof_1,`WeierstrassProjModel.kwYEvalRingHom._proof_2] do
    let some ci:=(← Lean.getEnv).find? n | throwError "missing proof cache seed"
    Lean.modifyEnv fun env =>Lean.Meta.auxLemmasExt.modifyState env fun st =>{ st with lemmas:=st.lemmas.insert { type:=ci.type,isPrivate:=false,defeq:=false } (n,ci.levelParams) }
open MvPolynomial in
def kwYEvalRingHom:ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0:R),1,0]) fun a ha =>by
    refine (Ideal.span_le.mpr ?_:Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff,SetLike.mem_coe,RingHom.mem_ker]
    exact WeierstrassCurve.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1:kwYEvalRingHom R W (q4 _ (X 1:MvPolynomial (Fin 3) R)) = 1:=by sorry
def kwYChartEval:HomogeneousLocalization.Away ((projModelGradingCR W.toProjective)) (q4 _ (MvPolynomial.X 1:MvPolynomial (Fin 3) R)) →+* R:=(IsLocalization.Away.lift (g:=kwYEvalRingHom R W) (q4 _ (MvPolynomial.X 1:MvPolynomial (Fin 3) R)) (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (HomogeneousLocalization.Away ((projModelGradingCR W.toProjective))
        (q4 _ (MvPolynomial.X 1:MvPolynomial (Fin 3) R))) (Localization.Away (q4 (projModelHomogeneousIdealCR W.toProjective).toIdeal (MvPolynomial.X 1:MvPolynomial (Fin 3) R))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap:(kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R:=by sorry
theorem kwYChartEval_section:(kwYChartEval R W).comp ((HomogeneousLocalization.fromZeroRingHom ((projModelGradingCR W.toProjective)) _).comp (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R:=by sorry
def kwZeroSect:SchemeHomOver (𝟙 (Spec (q2 R))) (projModelStrCR W.toProjective) :=
  ⟨q15 (q5 (kwYChartEval R W)) ≫
    Proj.awayι ((projModelGradingCR W.toProjective)) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR,Category.assoc]
    rw [← Category.assoc (Proj.awayι ..),Proj.awayι_toSpecZero,← Spec.map_comp,
      ← Spec.map_comp,← CommRingCat.ofHom_comp,← CommRingCat.ofHom_comp,
      kwYChartEval_section,CommRingCat.ofHom_id,Spec.map_id]⟩
eN 1 def schemeHomOverComp {B T' T A:q1} {t:T ⟶ B} {t':T' ⟶ B} {f:A ⟶ B} (ψ:T' ⟶ T) (hψ:ψ ≫ t = t') (x:SchemeHomOver t f):SchemeHomOver t' f :=
  ⟨ψ ≫ x.1,by rw [Category.assoc,x.2,hψ]⟩
@[simp]
theorem schemeHomOverComp_coe {B T' T A : q1} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 := rfl
structure RelativeGroupLaw (R:Type u) [CommRing R] {A:q1} (f:A ⟶ Spec (q2 R)) where
  mul:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f
  inv:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f → SchemeHomOver t f
  mul_assoc:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x y z:SchemeHomOver t f),mul t (mul t x y) z = mul t x (mul t y z)
  one_mul:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t (one t) x = x
  mul_one:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t x (one t) = x
  inv_mul_cancel:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t (inv t x) x = one t
  mul_natural:∀ {T T':q1} (t:T ⟶ Spec (q2 R)) (t':T' ⟶ Spec (q2 R)) (ψ:T' ⟶ T) (hψ:ψ ≫ t = t') (x y:SchemeHomOver t f),schemeHomOverComp ψ hψ (mul t x y) = mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
eN 1 namespace ArithmeticThetaRelativeKatoR0169
rC open NeronModelInfra
variable (R:Type u) [CommRing R]
abbrev Curve (W:WeierstrassCurve R):q1:=q66 W.toProjective
def structureMap (W:WeierstrassCurve R):Curve R W ⟶ Spec (q2 R):=q56 W.toProjective
def origin (W:WeierstrassCurve R):Spec (q2 R) ⟶ Curve R W:=(WeierstrassProjModel.kwZeroSect R W).val
abbrev Law (W:WeierstrassCurve R):=WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw (W:WeierstrassCurve R) (G:Law R W):Prop:=(∀ {V:q1} (t:V ⟶ Spec (q2 R)),(G.one t).val = t ≫ origin R W) ∧ (∀ {V:q1} (t:V ⟶ Spec (q2 R)) (x y:SchemeHomOver t (structureMap R W)),G.mul t x y = G.mul t y x)
eN 1 namespace WeierstrassProjModel.RelativeGroupLaw
rC open NeronModelInfra
variable {R:Type u} [CommRing R] {A:q1} {f:A ⟶ Spec (q2 R)}
def nsmul (G:RelativeGroupLaw R f) {T:q1} (t:T ⟶ Spec (q2 R)) (n:ℕ) (x:SchemeHomOver t f):SchemeHomOver t f:=Nat.rec (G.one t) (fun _ ih =>G.mul t ih x) n
eN 2 open NeronModelInfra
namespace GoodReductionJacobian
rC def schemeHomOverComp {B T' T A:q1} {t:T ⟶ B} {t':T' ⟶ B} {f:A ⟶ B} (ψ:T' ⟶ T) (hψ:ψ ≫ t = t') (x:SchemeHomOver t f):SchemeHomOver t' f :=
  ⟨ψ ≫ x.1,by rw [Category.assoc,x.2,hψ]⟩
structure RelativeGroupLaw (R:Type u) [CommRing R] {A:q1} (f:A ⟶ Spec (q2 R)) where
  mul:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f
  inv:∀ {T:q1} (t:T ⟶ Spec (q2 R)),SchemeHomOver t f → SchemeHomOver t f
  mul_assoc:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x y z:SchemeHomOver t f),mul t (mul t x y) z = mul t x (mul t y z)
  one_mul:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t (one t) x = x
  mul_one:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t x (one t) = x
  inv_mul_cancel:∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x:SchemeHomOver t f),mul t (inv t x) x = one t
  mul_natural:∀ {T T':q1} (t:T ⟶ Spec (q2 R)) (t':T' ⟶ Spec (q2 R)) (ψ:T' ⟶ T) (hψ:ψ ≫ t = t') (x y:SchemeHomOver t f),schemeHomOverComp ψ hψ (mul t x y) = mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
namespace RelativeGroupLaw
rC def IsCommutative {R:Type u} [CommRing R] {A:q1} {f:A ⟶ Spec (q2 R)} (G:RelativeGroupLaw R f):Prop:=∀ {T:q1} (t:T ⟶ Spec (q2 R)) (x y:SchemeHomOver t f),G.mul t x y = G.mul t y x
eN 1 eN 1 namespace GoodReductionJacobian.RelativeGroupLaw
rC variable {R:Type u} [CommRing R] {A:q1} {f:A ⟶ Spec (q2 R)}
def nsmul (G:RelativeGroupLaw R f) {T:q1} (t:T ⟶ Spec (q2 R)) (n:ℕ) (x:SchemeHomOver t f):SchemeHomOver t f:=Nat.rec (G.one t) (fun _ ih =>G.mul t ih x) n
abbrev idPoint:SchemeHomOver f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul (G:RelativeGroupLaw R f) (n:ℕ):A ⟶ A:=(G.nsmul f n idPoint).1
eN 2 namespace ArithmeticThetaRelativeDiscriminantR0171
rC abbrev Base (R:Type u) [CommRing R]:=Spec (q2 R)
eN 1 namespace ArithmeticThetaFullLevelCoverR0175
rC open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R:Type u) [CommRing R] (W:WeierstrassCurve R) (G:Law R W)
structure FullLevel (L:ℕ) {T:q1} (t:T ⟶ Base R) where
  x:SchemeHomOver t (structureMap R W)
  y:SchemeHomOver t (structureMap R W)
  killed_x:G.nsmul t L x = G.one t
  killed_y:G.nsmul t L y = G.one t
  avoids:∀ i j:Fin L,i.val ≠ 0 ∨ j.val ≠ 0 → Disjoint (q83 (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val) (q83 (origin R W))
structure LevelScheme (L:ℕ) where
  space:q1
  projection:space ⟶ Base R
  level:FullLevel R W G L projection
def Represents {L:ℕ} (D:LevelScheme R W G L):Prop:=∀ (T:q1) (t:T ⟶ Base R) (A:FullLevel R W G L t),∃! q:SchemeHomOver t D.projection,q.val ≫ D.level.x.val = A.x.val ∧ q.val ≫ D.level.y.val = A.y.val
def levelDegree (L:ℕ):ℕ:=Nat.card ((ZMod L × ZMod L) ≃+ (ZMod L × ZMod L))
eN 1 namespace ArithmeticThetaLegendreAtlasR0176
rC open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
abbrev LegendreRing (k:Type u) [Field k]:=Localization.Away (q74 * (q74 - 1):Polynomial k)
def parameter (k:Type u) [Field k]:LegendreRing k:=algebraMap (Polynomial k) (LegendreRing k) q74
def legendre (k:Type u) [Field k]:WeierstrassCurve (LegendreRing k) where
  a₁:=0
  a₂:=-(parameter k + 1)
  a₃:=0
  a₄:=parameter k
  a₆:=0
def legendreBaseMap (k:Type u) [Field k]:Base (LegendreRing k) ⟶ Base k:=q15 (q5 (algebraMap k (LegendreRing k)))
structure SignAction (R:Type u) [CommRing R] (W:WeierstrassCurve R) (G:Law R W) {L:ℕ} (Z:LevelScheme R W G L) where
  map:Z.space ⟶ Z.space
  over_eq:map ≫ Z.projection = Z.projection
  square:map ≫ map = 𝟙 _
  x_eq:map ≫ Z.level.x.val = (G.inv Z.projection Z.level.x).val
  y_eq:map ≫ Z.level.y.val = (G.inv Z.projection Z.level.y).val
  free:IsEmpty (equalizer map (𝟙 Z.space):q1)
structure SignQuotient (k:Type u) [Field k] {X:q1} (p:X ⟶ Base k) (σ:X ⟶ X) where
  ring:Type u
  [commRing:CommRing ring]
  [algebra:Algebra k ring]
  q:X ⟶ Base ring
  over_eq:q ≫ q15 (q5 (algebraMap k ring)) = p
  invariant:σ ≫ q = q
  finite:IsFinite q
  etale:Etale q
  surjective:Surjective q
  degree:∀ x,q.finrank x = 2
  smooth:SmoothOfRelativeDimension 1 (q15 (q5 (algebraMap k ring)))
  relation:(X ⨿ X) ≅ pullback q q
  left_fst:coprod.inl ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  left_snd:coprod.inl ≫ relation.hom ≫ pullback.snd q q = 𝟙 X
  right_fst:coprod.inr ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  right_snd:coprod.inr ≫ relation.hom ≫ pullback.snd q q = σ
  universal:∀ (T:q1) (a:X ⟶ T),σ ≫ a = a → ∃! b:Base ring ⟶ T,q ≫ b = a
attribute [instance] SignQuotient.commRing SignQuotient.algebra
abbrev coverCurve (R:Type u) [CommRing R] (W:WeierstrassCurve R) {G:Law R W} {L:ℕ} (Z:LevelScheme R W G L):=pullback (structureMap R W) Z.projection
abbrev coverToCurve (R:Type u) [CommRing R] (W:WeierstrassCurve R) {G:Law R W} {L:ℕ} (Z:LevelScheme R W G L):=pullback.fst (structureMap R W) Z.projection
abbrev coverToLevel (R:Type u) [CommRing R] (W:WeierstrassCurve R) {G:Law R W} {L:ℕ} (Z:LevelScheme R W G L):=pullback.snd (structureMap R W) Z.projection
def coverSection (R:Type u) [CommRing R] (W:WeierstrassCurve R) {G:Law R W} {L:ℕ} (Z:LevelScheme R W G L) (s:SchemeHomOver Z.projection (structureMap R W)):Z.space ⟶ coverCurve R W Z :=
  pullback.lift s.val (𝟙 _) (by simpa using s.property)
structure EllipticFamily (S:Type u) [CommRing S] where
  curve:q1
  projection:curve ⟶ Base S
  law:GoodReductionJacobian.RelativeGroupLaw S projection
  commutative:law.IsCommutative
  proper:IsProper projection
  smooth:SmoothOfRelativeDimension 1 projection
  connected:GeometricallyConnected projection
structure FamilyLevel (S:Type u) [CommRing S] (E:EllipticFamily S) (L:ℕ) where
  x:SchemeHomOver (𝟙 (Base S)) E.projection
  y:SchemeHomOver (𝟙 (Base S)) E.projection
  killed_x:x.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  killed_y:y.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  avoids:∀ i j:Fin L,i.val ≠ 0 ∨ j.val ≠ 0 → Disjoint (q83 (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i.val x) (E.law.nsmul (𝟙 _) j.val y)).val) (q83 (E.law.one (𝟙 _)).val)
def FamilyRigid (S:Type u) [CommRing S] (E:EllipticFamily S) {L:ℕ} (M:FamilyLevel S E L):Prop:=∀ e:E.curve ≅ E.curve,e.hom ≫ E.projection = E.projection → (E.law.one (𝟙 _)).val ≫ e.hom = (E.law.one (𝟙 _)).val → M.x.val ≫ e.hom = M.x.val → M.y.val ≫ e.hom = M.y.val → e.hom = 𝟙 E.curve
structure FamilyDescent (k R:Type u) [Field k] [CommRing R] [Algebra k R] (W:WeierstrassCurve R) (G:Law R W) {L:ℕ} (Z:LevelScheme R W G L) (σ:SignAction R W G Z) (Q:SignQuotient k (Z.projection ≫ q15 (q5 (algebraMap k R))) σ.map) where
  family:EllipticFamily Q.ring
  comparison:coverCurve R W Z ⟶ family.curve
  cartesian:IsPullback comparison (coverToLevel R W Z) family.projection Q.q
  origin_eq:coverSection R W Z (G.one Z.projection) ≫ comparison = Q.q ≫ (family.law.one (𝟙 _)).val
  action:coverCurve R W Z ⟶ coverCurve R W Z
  action_level:action ≫ coverToLevel R W Z = coverToLevel R W Z ≫ σ.map
  action_curve:action ≫ coverToCurve R W Z = (G.inv (coverToLevel R W Z ≫ Z.projection) ⟨coverToCurve R W Z,pullback.condition⟩).val
  invariant:action ≫ comparison = comparison
structure LegendreAtlas (k:Type u) [Field k] (L:ℕ) where
  law:Law (LegendreRing k) (legendre k)
  originLaw:IsOriginLaw (LegendreRing k) (legendre k) law
  level:LevelScheme (LegendreRing k) (legendre k) law L
  represents:Represents (LegendreRing k) (legendre k) law level
  sign:SignAction (LegendreRing k) (legendre k) law level
  quotient:SignQuotient k (level.projection ≫ legendreBaseMap k) sign.map
  descent:FamilyDescent k (LegendreRing k) (legendre k) law level sign quotient
  marking:FamilyLevel quotient.ring descent.family L
  rigid:FamilyRigid quotient.ring descent.family marking
  x_eq:coverSection (LegendreRing k) (legendre k) level level.level.x ≫ descent.comparison = quotient.q ≫ marking.x.val
  y_eq:coverSection (LegendreRing k) (legendre k) level level.level.y ≫ descent.comparison = quotient.q ≫ marking.y.val
eN 1 section Chart
open WeierstrassProjModel MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal
rC variable {T:Type u} [CommRing T] (W:q9 T)
abbrev coord (i:Fin 3):ProjModelRingCR W:=q4 (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i:Fin 3):coord W i ∈ projModelGradingCR W 1:=mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
abbrev ZChartRing:Type u:=Away (projModelGradingCR W) (coord W 2)
abbrev zChartι:Spec (q2 (ZChartRing W)) ⟶ projModelCR W:=Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos
def xOverZ:ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ:ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
eN 2 eN 1 namespace ArithmeticThetaLegendreComparisonR0177
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
abbrev ChartRing (R:Type u) [CommRing R] (W:WeierstrassCurve R):=WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R:Type u) [CommRing R] (W:WeierstrassCurve R):Spec (q2 (ChartRing R W)) ⟶ Curve R W:=WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R:Type u) [CommRing R] (W:WeierstrassCurve R):R →+* ChartRing R W:=(Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
def HasCoordinates (R:Type u) [CommRing R] (W:WeierstrassCurve R) (P:Base R ⟶ Curve R W) (x y:R):Prop:=P ≫ structureMap R W = 𝟙 (Base R) ∧ ∃ χ:ChartRing R W →+* R,P = q15 (q5 χ) ≫ chartInclusion R W ∧ χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = x ∧ χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = y
eN 1 namespace ArithmeticThetaCompatibleLevelR0178
rC open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177
variable (k:Type u) [Field k] [CharZero k] (L:ℕ) (A:LegendreAtlas k L)
abbrev TwoMarking:=FullLevel (LegendreRing k) (legendre k) A.law 2 (𝟙 (Base (LegendreRing k)))
def CanonicalTwo (B:TwoMarking k L A):Prop:=HasCoordinates (LegendreRing k) (legendre k) B.x.val 0 0 ∧ HasCoordinates (LegendreRing k) (legendre k) B.y.val 1 0
def CompatibleAt (B:TwoMarking k L A) {T:q1} (a:T ⟶ A.level.space):Prop:=a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.x).val = (a ≫ A.level.projection) ≫ B.x.val ∧ a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.y).val = (a ≫ A.level.projection) ≫ B.y.val
structure CompatibleCover (B:TwoMarking k L A) where
  space:q1
  inclusion:space ⟶ A.level.space
  openImmersion:IsOpenImmersion inclusion
  closedImmersion:IsClosedImmersion inclusion
  compatible:CompatibleAt k L A B inclusion
  represents:∀ (T:q1) (a:T ⟶ A.level.space),CompatibleAt k L A B a ↔ ∃! b:T ⟶ space,b ≫ inclusion = a
  finite:IsFinite (inclusion ≫ A.level.projection)
  etale:Etale (inclusion ≫ A.level.projection)
  surjective:Surjective (inclusion ≫ A.level.projection)
  degree:∀ z,(inclusion ≫ A.level.projection).finrank z = levelDegree L / 6
structure CompatibleQuotient (B:TwoMarking k L A) (C:CompatibleCover k L A B) where
  sign:C.space ⟶ C.space
  sign_eq:sign ≫ C.inclusion = C.inclusion ≫ A.sign.map
  sign_square:sign ≫ sign = 𝟙 _
  sign_free:IsEmpty (equalizer sign (𝟙 C.space):q1)
  quotient:SignQuotient k (C.inclusion ≫ A.level.projection ≫ legendreBaseMap k) sign
  inclusion:Base quotient.ring ⟶ Base A.quotient.ring
  cartesian:IsPullback C.inclusion quotient.q A.quotient.q inclusion
  openImmersion:IsOpenImmersion inclusion
  closedImmersion:IsClosedImmersion inclusion
  over_eq:inclusion ≫ q15 (q5 (algebraMap k A.quotient.ring)) = q15 (q5 (algebraMap k quotient.ring))
eN 1 namespace ArithmeticThetaProjectiveEffectivityR0135
rC attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace (S:Type u) [CommRing S] (N:ℕ):q1:=AlgebraicGeometry.Proj (q61 (Fin N) S)
def projectiveStructure (S:Type u) [CommRing S] (N:ℕ):projectiveSpace S N ⟶ Spec (q2 S):=Proj.toSpecZero (q61 (Fin N) S) ≫ q15 (q5 (algebraMap S ((q61 (Fin N) S) 0)))
eN 1 namespace ArithmeticThetaLevelCompactificationR0179
rC open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178
structure LevelData (k:Type u) [Field k] (L:ℕ) where
  atlas:LegendreAtlas k L
  two:TwoMarking k L atlas
  canonical:CanonicalTwo k L atlas two
  cover:CompatibleCover k L atlas two
  quotient:CompatibleQuotient k L atlas two cover
variable (k:Type u) [Field k] (L:ℕ)
abbrev OpenBase (D:LevelData k L):=Base D.quotient.quotient.ring
def openStructure (D:LevelData k L):OpenBase k L D ⟶ Base k:=q15 (q5 (algebraMap k D.quotient.quotient.ring))
structure Compactification (D:LevelData k L) where
  space:q1
  projection:space ⟶ Base k
  inclusion:OpenBase k L D ⟶ space
  over_eq:inclusion ≫ projection = openStructure k L D
  openImmersion:IsOpenImmersion inclusion
  dense:DenseRange inclusion.base
  proper:IsProper projection
  smooth:SmoothOfRelativeDimension 1 projection
  dimension:ℕ
  embedding:space ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)
  closedImmersion:IsClosedImmersion embedding
  embedding_over:embedding ≫ ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = projection
def boundary (D:LevelData k L) (X:Compactification k L D):Set X.space:=(q83 X.inclusion.base)ᶜ
eN 1 open TopologicalSpace MonoidalCategory
namespace WeierstrassProjModel.RelativeGroupLaw
rC open NeronModelInfra
variable {R:Type u} [CommRing R] {A:q1} {f:A ⟶ Spec (q2 R)}
abbrev idPoint:SchemeHomOver f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul (G:RelativeGroupLaw R f) (n:ℕ):A ⟶ A:=(G.nsmul f n idPoint).1
eN 2 namespace AlgebraicGeometry
rC structure Scheme.Modules.IsInvertible {X:q1} (M:X.Modules):Prop where
  exists_trivialization:∀ x:X,∃ (U:X.Opens),x ∈ U ∧ Nonempty ((q0 U.ι).obj M ≅ q24 U.toScheme.ringCatSheaf)
eN 1 namespace AlgebraicGeometry.Scheme.Hom
rC variable {A:Type u} [CommRing A] {X:q1} (f:X ⟶ Spec (q2 A))
def constToPresheaf:(Functor.const (X.Opens)ᵒᵖ).obj (q2 A) ⟶ X.presheaf where
  app U:=((Scheme.ΓSpecIso (q2 A))).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i:=by
    simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.id_comp,Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U:X.Opens):Algebra A Γ(X,U):=(f.constToPresheaf.app (op U)).hom.toAlgebra
def kaehlerPresheaf:X.PresheafOfModules:=q47 f.constToPresheaf
def kaehler:X.Modules:=(q13 (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf
def kaehlerToSections (U:X.Opens):(f.kaehlerPresheaf.obj (op U):Type u) → (Γ(f.kaehler,U):Type u):=fun s =>(((q6 (𝟙 X.ringCatSheaf.obj)).unit.app f.kaehlerPresheaf).app (op U)).hom s
eN 3 namespace AlgebraicGeometry.Scheme.Modules
rC variable {X Y:q1} (φ:X ⟶ Y) {L:Y.Modules} {U:Y.Opens}
def pullbackLocalSection (s:Γ(L,U)):Γ((Modules.pullback φ).obj L,φ ⁻¹ᵁ U):=((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s
eN 3 namespace ArithmeticThetaSheafTensor
rC variable (X:q1)
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor:MonoidalCategory X.PresheafOfModules:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def tensorPresheaf (H K:X.Modules):X.PresheafOfModules:=H.val ⊗ K.val
def sheafTensor (H K:X.Modules):X.Modules:=(q13 (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)
def tensorUnitMap (H K:X.Modules):tensorPresheaf X H K ⟶ (sheafTensor X H K).val:=(q6 (𝟙 X.ringCatSheaf.obj)).unit.app _
def tensorSection (H K:X.Modules) (U:X.Opens) (s:Γ(H,U)) (t:Γ(K,U)):Γ(sheafTensor X H K,U):=(tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X,U)] t)
eN 1 namespace ArithmeticThetaTensorPower
rC open ArithmeticThetaSheafTensor
def tensorPower (X:q1) (H:X.Modules):ℕ → X.Modules | 0 =>q24 X.ringCatSheaf | n + 1 =>sheafTensor X (tensorPower X H n) H
eN 1 namespace ArithmeticThetaRelativeDiscriminantR0171
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaTensorPower
abbrev Hodge (R:Type u) [CommRing R] (W:WeierstrassCurve R):=(q0 (origin R W)).obj (structureMap R W).kaehler
abbrev HodgePower (R:Type u) [CommRing R] (W:WeierstrassCurve R) (n:ℕ):=tensorPower (Base R) (Hodge R W) n
def res {X:q1} (F:X.Modules) {U V:X.Opens} (h:V ≤ U) (s:Γ(F,U)):Γ(F,V):=F.presheaf.map (homOfLE h).op s
def IsFrame {X:q1} (F:X.Modules) (U:X.Opens) (s:Γ(F,U)):Prop:=∀ (V:X.Opens) (h:V ≤ U),Function.Bijective (fun a:X.presheaf.obj (q30 V) =>a • res F h s)
def baseMap (R:Type u) [CommRing R] (S:Type u) [CommRing S] (ι:R →+* S):Base S ⟶ Base R:=q15 (q5 ι)
eN 1 namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
rC open TopologicalSpace
theorem T0.unitD._proof_1.{u_1}:∀ {X:q38},@CategoryTheory.Presheaf.IsLocallyInjective.{u_1,u_1,u_1,u_1 + 1,u_1,u_1} p9(X) p6(X) q81 RingCat.instCategory.{u_1} (fun (R S:q81) =>@RingHom.{u_1,u_1} (q12 R) (q12 S) p29(R) p26) q12 (fun (X Y:q81) =>@RingHom.instFunLike.{u_1, u_1} (q12 X) (q12 Y) p30(X) p27) RingCat.instConcreteCategoryRingHomCarrier.{u_1} p19(X) p3(X) p3(X) p25(X):=by sorry
theorem T0.unitD._proof_2.{u_1}:∀ {X:q38},@CategoryTheory.Presheaf.IsLocallySurjective.{u_1,u_1,u_1,u_1 + 1,u_1,u_1} p9(X) p6(X) p19(X) q81 RingCat.instCategory.{u_1} (fun (R S:q81) =>@RingHom.{u_1,u_1} (q12 R) (q12 S) p29(R) p26) q12 (fun (X Y:q81) =>@RingHom.instFunLike.{u_1, u_1} (q12 X) (q12 Y) p30(X) p27) RingCat.instConcreteCategoryRingHomCarrier.{u_1} p3(X) p3(X) p25(X):=by sorry
theorem T0.unitD._proof_3.{u_1}:∀ {X:q38},@CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.{u_1,u_1,u_1,u_1 + 1,u_1,u_1} p9(X) p6(X) p19(X) q85 AddCommGrpCat.instCategory.{u_1} (fun (x1 x2:q85) =>@AddMonoidHom.{u_1,u_1} (q3 x1) (q3 x2) (@AddZeroClass.toAddZero.{u_1} (q3 x1) (@AddMonoid.toAddZeroClass.{u_1} (q3 x1) (@SubNegMonoid.toAddMonoid.{u_1} (q3 x1) (@AddGroup.toSubNegMonoid.{u_1} (q3 x1) (@AddCommGroup.toAddGroup.{u_1} (q3 x1) (q65 x1)))))) (@AddZeroClass.toAddZero.{u_1} (q3 x2) (@AddMonoid.toAddZeroClass.{u_1} (q3 x2) (@SubNegMonoid.toAddMonoid.{u_1} (q3 x2) (@AddGroup.toSubNegMonoid.{u_1} (q3 x2) (@AddCommGroup.toAddGroup.{u_1} (q3 x2) (q65 x2))))))) q3 (fun (X Y:q85) =>@AddMonoidHom.instFunLike.{u_1,u_1} (q3 X) (q3 Y) (@AddZeroClass.toAddZero.{u_1} (q3 X) (@AddMonoid.toAddZeroClass.{u_1} (q3 X) (@SubNegMonoid.toAddMonoid.{u_1} (q3 X) (@AddGroup.toSubNegMonoid.{u_1} (q3 X) (@AddCommGroup.toAddGroup.{u_1} (q3 X) (q65 X)))))) (@AddZeroClass.toAddZero.{u_1} (q3 Y) (@AddMonoid.toAddZeroClass.{u_1} (q3 Y) (@SubNegMonoid.toAddMonoid.{u_1} (q3 Y) (@AddGroup.toSubNegMonoid.{u_1} (q3 Y) (@AddCommGroup.toAddGroup.{u_1} (q3 Y) (q65 Y))))))) AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{u_1}:=by sorry
theorem T0.unitD._proof_4.{u_1}:∀ {X:q38},@CategoryTheory.HasWeakSheafify.{u_1,u_1,u_1,u_1 + 1} p9(X) p6(X) p19(X) q85 AddCommGrpCat.instCategory.{u_1}:=by sorry
run_cmd do
  for n in [`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_1,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_2,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_3,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_4] do
    let some ci:=(← Lean.getEnv).find? n | throwError "missing proof cache seed"
    Lean.modifyEnv fun env =>Lean.Meta.auxLemmasExt.modifyState env fun st =>{ st with lemmas:=st.lemmas.insert { type:=ci.type,isPrivate:=false,defeq:=false } (n,ci.levelParams) }
section Main
variable {A B:Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y:q1} (gY:Y ⟶ Spec (q2 A)) (gX:X ⟶ Spec (q2 B))
    (φ:X ⟶ Y) (hφ:φ ≫ gY = gX ≫ q15 ((q5 (algebraMap A B)))) (d:ℕ)
include hφ
lemma fac (U:Y.Opens):q5 (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) = gY.constToPresheaf.app (op U) ≫ φ.app U:=by
  have h1:gY.constToPresheaf.app (op U) ≫ φ.app U =
      ((Scheme.ΓSpecIso (q2 A))).inv ≫ (φ ≫ gY).appLE ⊤ (φ ⁻¹ᵁ U) le_top:=by
    change (((Scheme.ΓSpecIso (q2 A))).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.app U = _
    rw [Category.assoc,← Scheme.Hom.appLE_eq_app,Scheme.Hom.appLE_comp_appLE]
  have h2:q5 (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      ((Scheme.ΓSpecIso (q2 A))).inv ≫
        (gX ≫ q15 ((q5 (algebraMap A B)))).appLE ⊤ (φ ⁻¹ᵁ U) le_top:=by
    change q5 (algebraMap A B) ≫
      ((Scheme.ΓSpecIso (q2 B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top) = _
    rw [Scheme.Hom.comp_appLE,← Category.assoc,Scheme.ΓSpecIso_inv_naturality,Category.assoc]
    rfl
  rw [h1,h2,hφ]
def kdMap (U:Y.Opens):gY.kaehlerPresheaf.obj (op U) ⟶ (ModuleCat.restrictScalars (φ.app U).hom).obj (gX.kaehlerPresheaf.obj (op (φ ⁻¹ᵁ U))):=CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
abbrev unit1 (V:X.Opens):gX.kaehlerPresheaf.obj (op V) ⟶ gX.kaehler.val.obj (op V):=((q6 (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf).app (op V)
omit hφ in
def dK {C:Type u} [CommRing C] {Z:q1} (g:Z ⟶ Spec (q2 C)) (V:Z.Opens) (b:Γ(Z,V)):(g.kaehlerPresheaf.obj (op V):Type u):=CommRingCat.KaehlerDifferential.d (f:=g.constToPresheaf.app (op V)) b
omit hφ in
lemma kp_map_dK {C:Type u} [CommRing C] {Z:q1} (g:Z ⟶ Spec (q2 C)) {V V':Z.Opens} (i:op V ⟶ op V') (b:Γ(Z,V)):g.kaehlerPresheaf.map i (dK g V b) = dK g V' (Z.presheaf.map i b):=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d g.constToPresheaf i b
omit hφ in
lemma kp_hom_ext {C:Type u} [CommRing C] {Z:q1} (g:Z ⟶ Spec (q2 C)) (V:Z.Opens) {M:ModuleCat Γ(Z,V)} {α β:g.kaehlerPresheaf.obj (op V) ⟶ M} (h:∀ b:Γ(Z,V),α (dK g V b) = β (dK g V b)):α = β:=CommRingCat.KaehlerDifferential.ext h
omit hφ in
lemma map_unit1 {V V':X.Opens} (j:op V ⟶ op V') (x:gX.kaehlerPresheaf.obj (op V)):gX.kaehler.val.map j (unit1 gX V x) = unit1 gX V' (gX.kaehlerPresheaf.map j x):=(PresheafOfModules.naturality_apply ((q6 (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf) j x).symm
omit hφ in
lemma φ_naturality_apply {U U':Y.Opens} (i:op U ⟶ op U') (b:Γ(Y,U)):X.presheaf.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op (φ.app U b) = φ.app U' (Y.presheaf.map i b):=(CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm
def k1app (U:Y.Opens):gY.kaehlerPresheaf.obj (op U) ⟶ ((q52 φ).obj gX.kaehler).val.obj (op U):=kdMap gY gX φ hφ U ≫ (ModuleCat.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))
lemma k1app_dK (U:Y.Opens) (b:Γ(Y,U)):k1app gY gX φ hφ U (dK gY U b) = unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)):=by
  show unit1 gX (φ ⁻¹ᵁ U) (CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
    (CommRingCat.KaehlerDifferential.d b)) = _
  rw [CommRingCat.KaehlerDifferential.map_d]
  rfl
def k1pre:gY.kaehlerPresheaf ⟶ ((q52 φ).obj gX.kaehler).val where
  app U:=k1app gY gX φ hφ U.unop
  naturality {U U'} i:=by
    obtain ⟨U⟩:=U; obtain ⟨U'⟩:=U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b)) =
      gX.kaehler.val.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK,k1app_dK,k1app_dK,map_unit1,kp_map_dK,φ_naturality_apply]
abbrev adjY:=q6 (𝟙 Y.ringCatSheaf.obj)
def k1:gY.kaehler ⟶ (q52 φ).obj gX.kaehler:=((adjY (Y:=Y)).homEquiv gY.kaehlerPresheaf ((q52 φ).obj gX.kaehler)).symm (k1pre gY gX φ hφ)
eN 1 eN 3 namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
rC open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
section DifferentialMap
variable {A B:Type u} [CommRing A] [CommRing B] [Algebra A B] {X Y:q1}
    (gY:Y ⟶ Spec (q2 A)) (gX:X ⟶ Spec (q2 B)) (φ:X ⟶ Y)
    (hφ:φ ≫ gY = gX ≫ q15 ((q5 (algebraMap A B))))
def differentialMap:(q0 φ).obj gY.kaehler ⟶ gX.kaehler:=((q22 φ).homEquiv _ _).symm (k1 gY gX φ hφ)
theorem differentialMap_isIso (hc:CategoryTheory.IsPullback φ gX gY (q15 ((q5 (algebraMap A B))))) [SmoothOfRelativeDimension 1 gY]:IsIso (differentialMap gY gX φ hφ):=by sorry
eN 1 variable {X Y:q1}
def pullbackEqIso {f g:X ⟶ Y} (h:f = g) (M:Y.Modules):(q0 f).obj M ≅ (q0 g).obj M :=
  eqToIso (by cases h; rfl)
def squarePullbackIso {A B X Y:q1} (a:A ⟶ B) (s:B ⟶ Y) (t:A ⟶ X) (b:X ⟶ Y) (h:a ≫ s = t ≫ b) (M:Y.Modules):(q0 a).obj ((q0 s).obj M) ≅ (q0 t).obj ((q0 b).obj M):=(q7 a s).app M ≪≫ pullbackEqIso h M ≪≫ ((q7 t b).app M).symm
section PointedComparison
variable {A B:Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y:q1} (gY:Y ⟶ Spec (q2 A))
    (gX:X ⟶ Spec (q2 B)) (φ:X ⟶ Y)
    (hc:CategoryTheory.IsPullback φ gX gY (q15 ((q5 (algebraMap A B)))))
    [SmoothOfRelativeDimension 1 gY]
    (s:Spec (q2 A) ⟶ Y) (t:Spec (q2 B) ⟶ X)
    (hpt:t ≫ φ = q15 ((q5 (algebraMap A B))) ≫ s)
def pointedDifferentialIso:(q0 (q15 ((q5 (algebraMap A B))))).obj ((q0 s).obj gY.kaehler) ≅ (q0 t).obj gX.kaehler:=by
  letI:=differentialMap_isIso gY gX φ hc.w hc
  exact squarePullbackIso _ s t φ hpt.symm gY.kaehler ≪≫
    (q0 t).mapIso (asIso (differentialMap gY gX φ hc.w))
eN 1 eN 2 namespace ArithmeticThetaOpenHodgeR0180
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
abbrev zero {S:Type u} [CommRing S] (E:EllipticFamily S):Base S ⟶ E.curve:=(E.law.one (𝟙 _)).val
abbrev hodge {S:Type u} [CommRing S] (E:EllipticFamily S):=(q0 (zero E)).obj E.projection.kaehler
abbrev power {S:Type u} [CommRing S] (E:EllipticFamily S) (n:ℕ):=tensorPower (Base S) (hodge E) n
structure Test (S:Type u) [CommRing S] (E:EllipticFamily S) (R:Type u) [CommRing R] (W:WeierstrassCurve R) (G:Law R W) where
  scalar:S →+* R
  map:Curve R W ⟶ E.curve
  cartesian:IsPullback map (structureMap R W) E.projection (baseMap S R scalar)
  origin_eq:origin R W ≫ map = baseMap S R scalar ≫ zero E
  nsmul_eq:∀ n,G.schemeNsmul n ≫ map = map ≫ E.law.schemeNsmul n
def comparison {S R:Type u} [CommRing S] [CommRing R] {E:EllipticFamily S} {W:WeierstrassCurve R} {G:Law R W} (C:Test S E R W G):(q0 (baseMap S R C.scalar)).obj (hodge E) ≅ Hodge R W:=by
  letI:Algebra S R:=C.scalar.toAlgebra
  letI:SmoothOfRelativeDimension 1 E.projection:=E.smooth
  exact pointedDifferentialIso E.projection (structureMap R W) C.map
    C.cartesian (zero E) (origin R W) C.origin_eq
eN 1 namespace ArithmeticThetaCompatibleLevelR0178
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175
variable (k:Type u) [Field k] (L:ℕ) (A:q21 k L)
def Classifies (B:TwoMarking k L A) (C:CompatibleCover k L A B) (Q:CompatibleQuotient k L A B C) (R:Type u) [CommRing R] [Algebra k R] (W:WeierstrassCurve R) (G:Law R W) (M:FullLevel R W G L (𝟙 (Base R))) (b:Base R ⟶ Base Q.quotient.ring) (f:Curve R W ⟶ A.descent.family.curve):Prop:=b ≫ q15 (q5 (algebraMap k Q.quotient.ring)) =
    q15 (q5 (algebraMap k R)) ∧ IsPullback f (structureMap R W) A.descent.family.projection (b ≫ Q.inclusion) ∧ origin R W ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val ∧ M.x.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.x.val ∧ M.y.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.y.val
eN 1 namespace ArithmeticThetaTateSeries
rC variable {k:Type u} [Field k]
def monomial (a:k) (n:ℕ):PowerSeries k:=PowerSeries.C a * PowerSeries.X ^ n
def xTerm (v:PowerSeries k):PowerSeries k:=v * ((1-v)⁻¹)^2
def yTerm (v:PowerSeries k):PowerSeries k:=v * (1+v) * ((1-v)⁻¹)^3
def partialX (d i:ℕ) (a:k) (N:ℕ):PowerSeries k:=xTerm (monomial a i) + (∑ j ∈ Finset.range N,(xTerm (monomial a (d*(j+1)+i)) + xTerm (monomial a⁻¹ (d*(j+1)-i)))) - 2 * ∑ j ∈ Finset.range N,PowerSeries.C ((j+1:ℕ):k) * monomial 1 (d*(j+1)) * (1 - monomial 1 (d*(j+1)))⁻¹
def partialY (d i:ℕ) (a:k) (N:ℕ):PowerSeries k:=PowerSeries.C (2:k)⁻¹ * (yTerm (monomial a i) + ∑ j ∈ Finset.range N,(yTerm (monomial a (d*(j+1)+i)) - yTerm (monomial a⁻¹ (d*(j+1)-i))))
def tateX (d i:ℕ) (a:k):PowerSeries k:=PowerSeries.mk fun n =>PowerSeries.coeff n (partialX d i a (n+1))
def tateY (d i:ℕ) (a:k):PowerSeries k:=PowerSeries.mk fun n =>PowerSeries.coeff n (partialY d i a (n+1))
eN 1 namespace ArithmeticThetaCubicModelR0144
rC variable (k:Type u) [Field k] [CharZero k]
def rootSeries (r:ℕ) (j:Fin 3):PowerSeries k:=if j.val = 0 then q72 r 0 (-1) else q72 r (r/2) (if j.val = 1 then 1 else -1)
eN 1 namespace ArithmeticThetaCompactifiedDifferentialR0145
rC open ArithmeticThetaCubicModelR0144
variable (k:Type u) [Field k] [CharZero k]
def root (r:ℕ) (j:Fin 3):LaurentSeries k:=algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k r j)
def curve (r:ℕ):WeierstrassCurve (LaurentSeries k) where
  a₁:=0
  a₂:=-(root k r 0 + root k r 1 + root k r 2)
  a₃:=0
  a₄:=root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2
  a₆:=-(root k r 0 * root k r 1 * root k r 2)
abbrev projectiveCurve (r:ℕ):q1:=q66 (curve k r).toProjective
def projectiveStructure (r:ℕ):projectiveCurve k r ⟶ Spec (q2 (LaurentSeries k)):=q56 (curve k r).toProjective
abbrev ChartRing (r:ℕ):=WeierstrassCurve.DrinfeldGlobal.ZChartRing (curve k r).toProjective
def chartInclusion (r:ℕ):Spec (q2 (ChartRing k r)) ⟶ projectiveCurve k r:=WeierstrassCurve.DrinfeldGlobal.zChartι (curve k r).toProjective
def relativeD {F:Type u} [CommRing F] {C:q1} (f:C ⟶ Spec (q2 F)) (U:C.Opens) (a:C.presheaf.obj (q30 U)):Γ(f.kaehler,U) :=
  letI:Algebra F (C.presheaf.obj (q30 U)):=f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (q30 U)) a)
eN 1 namespace ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart
rC open HomogeneousLocalization WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
variable (k:Type u) [Field k] [CharZero k] (r:ℕ)
def chartScalar:LaurentSeries k →+* ChartRing k r:=(HomogeneousLocalization.fromZeroRingHom (projModelGradingCR (curve k r).toProjective) (Submonoid.powers (coord (curve k r).toProjective 2))).comp (algebraMap (LaurentSeries k) (projModelGradingCR (curve k r).toProjective 0))
eN 2 namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
rC section ChartEquiv
variable {B:Type u} [CommRing B] {C:q1} (i:Spec (q2 B) ⟶ C) [IsOpenImmersion i]
def chartRingEquiv:Γ(C,i ''ᵁ ⊤) ≃+* B:=((i.appIso ⊤) ≪≫ Scheme.ΓSpecIso (q2 B)).commRingCatIsoToRingEquiv
eN 1 variable (k:Type u) [Field k] [CharZero k] (r:ℕ)
local instance zchartAlgebra:Algebra (LaurentSeries k) (ChartRing k r):=(ProjectiveCubicChart.chartScalar k r).toAlgebra
variable {C:q1} (E:C ≅ projectiveCurve k r)
abbrev zLeg:=chartInclusion k r ≫ E.inv
instance zLeg_open:IsOpenImmersion (zLeg k r E):=by dsimp [zLeg,chartInclusion]; infer_instance
abbrev zOpen:C.Opens:=zLeg k r E ''ᵁ ⊤
abbrev zSection:ChartRing k r ≃+* Γ(C,zOpen k r E):=(chartRingEquiv (zLeg k r E)).symm
eN 2 namespace ArithmeticThetaTateCuspsR0181
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLevelCompactificationR0179
variable (k:Type u) [Field k] [CharZero k] (L:ℕ)
abbrev TateCurve:=ArithmeticThetaCompactifiedDifferentialR0145.curve k L
abbrev Disk:=Base (PowerSeries k)
abbrev Puncture:=Base (LaurentSeries k)
def genericInclusion:Puncture k ⟶ Disk k:=q15 (q5 (algebraMap (PowerSeries k) (LaurentSeries k)))
def diskStructure:Disk k ⟶ Base k:=q15 (q5 (algebraMap k (PowerSeries k)))
def closedPoint:Disk k:=⟨IsLocalRing.maximalIdeal (PowerSeries k),inferInstance⟩
structure TateLevel where
  elliptic:(TateCurve k L).IsElliptic
  law:Law (LaurentSeries k) (TateCurve k L)
  originLaw:IsOriginLaw (LaurentSeries k) (TateCurve k L) law
  marking:FullLevel (LaurentSeries k) (TateCurve k L) law L (𝟙 (Puncture k))
def Extends (D:LevelData k L) (X:Compactification k L D) (b:Puncture k ⟶ OpenBase k L D) (d:Disk k ⟶ X.space):Prop:=d ≫ X.projection = diskStructure k ∧ genericInclusion k ≫ d = b ≫ X.inclusion ∧ d (closedPoint k) ∈ boundary k L D X
eN 1 namespace ArithmeticThetaBoundaryHodgeR0182
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
variable (k:Type) [Field k] [CharZero k] (L:ℕ)
abbrev CurveFrame:=(q24 (Curve (LaurentSeries k) (TateCurve k L)).ringCatSheaf:(Curve (LaurentSeries k) (TateCurve k L)).Modules) ≅ (structureMap (LaurentSeries k) (TateCurve k L)).kaehler
def Normalized (δ:CurveFrame k L):Prop :=
  let E:=Iso.refl (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k L)
  let U:=ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen k L E
  let x:=q39 k L E
    (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)
  let y:=q39 k L E
    (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)
  q80
    (structureMap (LaurentSeries k) (TateCurve k L)) U x =
      (2*y) • Scheme.Modules.Hom.app δ.hom U (1:Γ(Curve (LaurentSeries k) (TateCurve k L),U))
def hodgeGenerator (δ:CurveFrame k L):Γ(Hodge (LaurentSeries k) (TateCurve k L),⊤) :=
  res _ (by simp) (q10
    (origin (LaurentSeries k) (TateCurve k L)) (Scheme.Modules.Hom.app δ.hom ⊤ (1:Γ(Curve (LaurentSeries k) (TateCurve k L),⊤))))
structure Test (D:LevelData k L) where
  level:TateLevel k L
  base:Puncture k ⟶ OpenBase k L D
  map:Curve (LaurentSeries k) (TateCurve k L) ⟶ D.atlas.descent.family.curve
  classifies:ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two D.cover D.quotient (LaurentSeries k) (TateCurve k L) level.law level.marking base map
  nsmul_eq:∀ n,level.law.schemeNsmul n ≫ map = map ≫ D.atlas.descent.family.law.schemeNsmul n
  differential:CurveFrame k L
  normalized:Normalized k L differential
structure DiskTest (D:LevelData k L) (X:Compactification k L D) extends Test k L D where
  disk:Disk k ⟶ X.space
  extends_eq:Extends k L D X base disk
abbrev openHodge (D:LevelData k L):=(q0 D.quotient.inclusion).obj (hodge D.atlas.descent.family)
abbrev openPower (D:LevelData k L) (n:ℕ):=tensorPower (OpenBase k L D) (openHodge k L D) n
def testIso {D:LevelData k L} (T:Test k L D):(q0 (T.base ≫ D.quotient.inclusion)).obj (hodge D.atlas.descent.family) ≅ Hodge (LaurentSeries k) (TateCurve k L):=by
  let ι:D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
  have hmap:baseMap D.atlas.quotient.ring (LaurentSeries k) ι =
      T.base ≫ D.quotient.inclusion:=Spec.map_preimage _
  let C:ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring
      D.atlas.descent.family (LaurentSeries k) (TateCurve k L) T.level.law :=
    { scalar:=ι
      map:=T.map
      cartesian:=by rw [hmap]; exact T.classifies.2.1
      origin_eq:=by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq:=T.nsmul_eq }
  exact pullbackEqIso hmap.symm (hodge D.atlas.descent.family) ≪≫ comparison C
def openTestIso {D:LevelData k L} (T:Test k L D):(q0 T.base).obj (openHodge k L D) ≅ Hodge (LaurentSeries k) (TateCurve k L):=(q7 T.base D.quotient.inclusion).app _ ≪≫ testIso k L T
structure Extension (D:LevelData k L) (X:Compactification k L D) where
  line:X.space.Modules
  invertible:Scheme.Modules.IsInvertible line
  onOpen:(q0 X.inclusion).obj line ≅ openHodge k L D
def diskGenericIso {D:LevelData k L} {X:Compactification k L D} (H:Extension k L D X) (T:DiskTest k L D X):(q0 (genericInclusion k)).obj ((q0 T.disk).obj q58) ≅ Hodge (LaurentSeries k) (TateCurve k L):=(q7 (genericInclusion k) T.disk).app q58 ≪≫ pullbackEqIso T.extends_eq.2.1 q58 ≪≫
    ((q7 T.base X.inclusion).app q58).symm ≪≫ (q0 T.base).mapIso H.onOpen ≪≫ openTestIso k L T.toTest
def ExtendsGenerator {D:LevelData k L} {X:Compactification k L D} (H:Extension k L D X) (T:DiskTest k L D X) (η:Γ((q0 T.disk).obj q58,⊤)):Prop :=
  IsFrame ((q0 T.disk).obj q58) ⊤ η ∧
  res _ (by simp) ((diskGenericIso k L H T).hom.app _
    (q10 (genericInclusion k) η)) =
      hodgeGenerator k L T.differential
def Canonical {D:LevelData k L} {X:Compactification k L D} (H:Extension k L D X):Prop:=∀ T:DiskTest k L D X,∃! η:Γ((q0 T.disk).obj q58,⊤),ExtendsGenerator k L H T η
eN 1 namespace ArithmeticThetaSheafTensor
rC variable (X:q1)
eN 1 namespace ArithmeticThetaTensorPower
rC open ArithmeticThetaSheafTensor
def tensorPowerSection (X:q1) (H:X.Modules):(n:ℕ) → (U:X.Opens) → Γ(H,U) → Γ(tensorPower X H n,U) | 0,U,_ =>(1:Γ(X,U)) | n + 1,U,s =>tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s
eN 1 namespace ArithmeticThetaPalomarBinaryTensor458
rC open ArithmeticThetaSheafTensor
def pullSection {X Y:q1} (f:X ⟶ Y) {H:Y.Modules} {U:Y.Opens} (s:Γ(H,U)):Γ((q0 f).obj H,f ⁻¹ᵁ U):=((q22 f).unit.app H).app U s
def Compatible {X Y:q1} (f:X ⟶ Y) (H K:Y.Modules) (M N:X.Modules) (e:(q0 f).obj H ≅ M) (d:(q0 f).obj K ≅ N) (q:(q0 f).obj (sheafTensor Y H K) ≅ sheafTensor X M N):Prop :=
  ∀ (U:Y.Opens) (s:Γ(H,U)) (t:Γ(K,U)),q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) = tensorSection X M N (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y:q1} (f:X ⟶ Y) (H K:Y.Modules) (M N:X.Modules) (e:(q0 f).obj H ≅ M) (d:(q0 f).obj K ≅ N):∃! q:(q0 f).obj (sheafTensor Y H K) ≅ sheafTensor X M N,Compatible f H K M N e d q:=by sorry
eN 1 namespace ArithmeticThetaPullback
rC
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
def pullback_unit_iso (X Y:q1) (p:X ⟶ Y):(q0 p).obj (q24 Y.ringCatSheaf) ≅ q24 X.ringCatSheaf:=by
  letI:(TopologicalSpace.Opens.map p.base).Final:=by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤,by simp⟩
  let e:=asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
eN 1 namespace ArithmeticThetaPalomarHalf505
rC open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y:q1} (f:X ⟶ Y) (H K:Y.Modules):(q0 f).obj (sheafTensor Y H K) ≅ sheafTensor X ((q0 f).obj H) ((q0 f).obj K):=Classical.choose (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
eN 1 namespace ArithmeticThetaPullback
rC open ArithmeticThetaSheafTensor
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor (X:q1):MonoidalCategory X.PresheafOfModules:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def sheafTensorMap (X:q1) {H H' K K':X.Modules} (f:H ⟶ H') (g:K ⟶ K'):sheafTensor X H K ⟶ sheafTensor X H' K':=(q13 (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)
def sheafTensorCongr (X:q1) {H H' K K':X.Modules} (e:H ≅ H') (d:K ≅ K'):sheafTensor X H K ≅ sheafTensor X H' K':=(q13 (𝟙 X.ringCatSheaf.obj)).mapIso (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso d))
eN 1 namespace ArithmeticThetaPalomarHalf505
rC open ArithmeticThetaTensorPower
def powerComparison (X Y:q1) (f:X ⟶ Y) (H:Y.Modules):(n:ℕ) → (q0 f).obj (tensorPower Y H n) ≅ tensorPower X ((q0 f).obj H) n | 0 =>ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 =>binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
eN 1 namespace ArithmeticThetaGeometricNormR0150
rC variable {X Y:q1} [IsIntegral X] [IsIntegral Y]
def IsFieldMap (f:X ⟶ Y) (φ:Y.functionField →+* X.functionField):Prop:=X.fromSpecStalk (genericPoint X) ≫ f = q15 (q5 φ) ≫ Y.fromSpecStalk (genericPoint Y)
def fieldNorm (φ:Y.functionField →+* X.functionField) (g:X.functionField):Y.functionField :=
  letI:=φ.toAlgebra
  Algebra.norm Y.functionField g
eN 1 namespace ArithmeticThetaGeneralEllipticKatoR0168
rC open NeronModelInfra
variable (F:Type u) [Field F]
abbrev Curve (W:WeierstrassCurve F):q1:=q66 W.toProjective
def structureMap (W:WeierstrassCurve F):Curve F W ⟶ Spec (q2 F):=q56 W.toProjective
def origin (W:WeierstrassCurve F):Spec (q2 F) ⟶ Curve F W:=(WeierstrassProjModel.kwZeroSect F W).val
abbrev Law (W:WeierstrassCurve F):=WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)
def IsOriginLaw (W:WeierstrassCurve F) (G:Law F W):Prop:=(∀ {V:q1} (t:V ⟶ Spec (q2 F)),(G.one t).val = t ≫ origin F W) ∧ (∀ {V:q1} (t:V ⟶ Spec (q2 F)) (x y:SchemeHomOver t (structureMap F W)),G.mul t x y = G.mul t y x)
section
attribute [local instance 2000] HenselianLocalRing.toIsLocalRing
def originPoint (W:WeierstrassCurve F):Curve F W:=origin F W (IsLocalRing.closedPoint F)
end
def katoOrder (W:WeierstrassCurve F) (G:Law F W) (c:ℕ) (x:Curve F W):ℤ:=by
  classical
  exact (if x = originPoint F W then (c:ℤ)^2 else 0) - (if G.schemeNsmul c x = originPoint F W then 1 else 0)
def HasKatoDivisor (W:WeierstrassCurve F) (G:Law F W) (c:ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g:(Curve F W).functionField):Prop:=g ≠ 0 ∧ ∀ x:Curve F W,Scheme.ord g x = katoOrder F W G c x
def IsKatoFunction (W:WeierstrassCurve F) (G:Law F W) (c:ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g:(Curve F W).functionField):Prop:=HasKatoDivisor F W G c g ∧ ∀ d:ℕ,0 < d → Nat.Coprime c d → ∀ φ:(Curve F W).functionField →+* (Curve F W).functionField,q37 (G.schemeNsmul d) φ →
          ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g
eN 1 namespace ArithmeticThetaRelativeKatoR0169
rC variable (R:Type u) [CommRing R] [IsDomain R]
abbrev GenericCurve (W:WeierstrassCurve R):q1:=ArithmeticThetaGeneralEllipticKatoR0168.Curve (FractionRing R) (W.map ((algebraMap R (FractionRing R))))
structure GenericComparison (W:WeierstrassCurve R) (G:Law R W) [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)] where
  law:ArithmeticThetaGeneralEllipticKatoR0168.Law (FractionRing R) (W.map ((algebraMap R (FractionRing R))))
  originLaw:ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (FractionRing R) (W.map ((algebraMap R (FractionRing R)))) law
  map:GenericCurve R W ⟶ Curve R W
  cartesian:IsPullback map (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (FractionRing R) (W.map ((algebraMap R (FractionRing R))))) (structureMap R W) (q15 (q5 ((algebraMap R (FractionRing R)))))
  origin_eq:ArithmeticThetaGeneralEllipticKatoR0168.origin (FractionRing R) (W.map ((algebraMap R (FractionRing R)))) ≫ map = q15 (q5 ((algebraMap R (FractionRing R)))) ≫ origin R W
  multiplication_eq:∀ n:ℕ,law.schemeNsmul n ≫ map = map ≫ G.schemeNsmul n
  field:(Curve R W).functionField ≃+* (GenericCurve R W).functionField
  field_eq:q37 map field.toRingHom
def katoOrder (W:WeierstrassCurve R) (G:Law R W) (c:ℕ) (x:Curve R W):ℤ:=by
  classical
  exact (if x ∈ q83 (origin R W) then (c:ℤ)^2 else 0) - (if G.schemeNsmul c x ∈ q83 (origin R W) then 1 else 0)
variable (W:WeierstrassCurve R) (G:Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
def IsRelativeKato (c:ℕ) (g:(Curve R W).functionField):Prop:=g ≠ 0 ∧ (∀ x:Curve R W,Order.coheight x = 1 → Scheme.ord g x = katoOrder R W G c x) ∧ (∀ d:ℕ,0 < d → Nat.Coprime c d → ∀ φ:(Curve R W).functionField →+* (Curve R W).functionField,q37 (G.schemeNsmul d) φ → ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g)
eN 1 namespace ArithmeticThetaRelativeKatoNaturalityR0170
rC open ArithmeticThetaRelativeKatoR0169
variable (R:Type u) [CommRing R] [IsDomain R]
variable (W:WeierstrassCurve R) (G:Law R W)
def identityIdeal:(Curve R W).IdealSheafData:=(origin R W).ker
def torsionIdeal (n:ℕ):(Curve R W).IdealSheafData:=(identityIdeal R W).comap (G.schemeNsmul n)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
variable [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
def Normalized (c:ℕ) (g:(Curve R W).functionField):Prop:=IsRelativeKato R W G c g ∧ ∀ C:GenericComparison R W G,ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R) (W.map ((algebraMap R (FractionRing R)))) C.law c (C.field g)
def HasValue (P:Spec (q2 R) ⟶ Curve R W) (g:(Curve R W).functionField) (v:R):Prop:=∃ (U:(Curve R W).Opens) (hU:Nonempty U) (e:(⊤:(Spec (q2 R)).Opens) ≤ P ⁻¹ᵁ U) (a:(Curve R W).presheaf.obj (q30 U)),IsUnit a ∧ @Scheme.germToFunctionField (Curve R W) _ U hU a = g ∧ (Scheme.ΓSpecIso (q2 R)).hom (P.appLE U ⊤ e a) = v
eN 1 namespace ArithmeticThetaRelativeDiscriminantR0171
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaTensorPower
def localDifferential (R:Type u) [CommRing R] (W:WeierstrassCurve R) (U:(Curve R W).Opens) (a:(Curve R W).presheaf.obj (q30 U)):Γ(Hodge R W,(origin R W) ⁻¹ᵁ U):=q10 (origin R W) (q80 (structureMap R W) U a)
def localPower (R:Type u) [CommRing R] (W:WeierstrassCurve R) (n:ℕ) (U:(Curve R W).Opens) (a:(Curve R W).presheaf.obj (q30 U)):Γ(HodgePower R W n,(origin R W) ⁻¹ᵁ U):=tensorPowerSection (Base R) (Hodge R W) n ((origin R W) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R:Type u) [CommRing R] [IsDomain R]
variable (W:WeierstrassCurve R) (G:Law R W)
def IdentityChart (c:ℕ) (U:(Curve R W).affineOpens) (a:(Curve R W).presheaf.obj (q30 U.1)):Prop:=IsRegular a ∧ (identityIdeal R W).ideal U = Ideal.span ({a}:Set _) ∧ (torsionIdeal R W G c).ideal U = (identityIdeal R W).ideal U
variable [IsIntegral (Curve R W)]
def RepresentsInitial (c:ℕ) (g:(Curve R W).functionField) (d:Γ(HodgePower R W (c^2-1),⊤)):Prop:=∀ (U:(Curve R W).affineOpens) [Nonempty U.1] (a:(Curve R W).presheaf.obj (q30 U.1)),IdentityChart R W G c U a → ∃ ε:((Curve R W).presheaf.obj (q30 U.1))ˣ,(c:(Curve R W).functionField) * g = (Curve R W).germToFunctionField U.1 ((ε:_) * a^(c^2-1)) ∧
      res (HodgePower R W (c^2-1)) le_top d = (origin R W).app U.1 (ε:_) • localPower R W (c^2-1) U.1 a
eN 1 namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
rC open ArithmeticThetaPullback ArithmeticThetaTensorPower
def powerCongr (X:q1) {H K:X.Modules} (e:H ≅ K):(n:ℕ) → tensorPower X H n ≅ tensorPower X K n | 0 =>Iso.refl _ | n + 1 =>sheafTensorCongr X (powerCongr X e n) e
eN 2 namespace ArithmeticThetaPullback
rC def pullbackGlobalSection {X Y:q1} (p:X ⟶ Y) (M:Y.Modules):Γ(M,⊤) → Γ((q0 p).obj M,p ⁻¹ᵁ (⊤:Y.Opens)):=fun s =>((q22 p).unit.app M).app ⊤ s
eN 1 namespace ArithmeticThetaPalomarD2_509.HodgeBaseChange
rC open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
def tensorComparison {X Y:q1} (p:X ⟶ Y) (H:Y.Modules) (K:X.Modules) (e:(q0 p).obj H ≅ K) (n:ℕ):(q0 p).obj (tensorPower Y H n) ≅ tensorPower X K n:=q35 X Y p H n ≪≫ powerCongr X e n
eN 2 namespace ArithmeticThetaPalomarD2_509.OpenHodge
rC open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower ArithmeticThetaOpenHodgeR0180
def powerComparison {S R:Type u} [CommRing S] [CommRing R] {E:EllipticFamily S} {W:WeierstrassCurve R} {G:Law R W} (C:Test S E R W G) (n:ℕ):(q0 (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n:=q67 (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n
def pullSection {S R:Type u} [CommRing S] [CommRing R] {E:EllipticFamily S} {W:WeierstrassCurve R} {G:Law R W} (C:Test S E R W G) (n:ℕ) (s:Γ(power E n,⊤)):Γ(HodgePower R W n,⊤) :=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (q10 (baseMap S R C.scalar) s))
def IsD2 {S:Type u} [CommRing S] (E:EllipticFamily S) (d:Γ(power E 24,⊤)):Prop:=IsFrame (power E 24) ⊤ d ∧ ∀ (R:Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W:WeierstrassCurve R) [W.IsElliptic] [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)] [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G:Law R W),IsOriginLaw R W G → ∀ (C:Test S E R W G) (g:(Curve R W).functionField),Normalized R W G 5 g → RepresentsInitial R W G 5 g (pullSection C 24 d)
eN 2 namespace ArithmeticThetaPalomarD2_509.BoundaryHodge
rC open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171
variable (k:Type) [Field k] [CharZero k] (L:ℕ)
def pullToOpen {D:LevelData k L} (n:ℕ) (s:Γ(power D.atlas.descent.family n,⊤)):Γ(openPower k L D n,⊤) :=
  res _ (by simp) ((q35 _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (q10 D.quotient.inclusion s))
def restrictPower {D:LevelData k L} {X:Compactification k L D} (H:Extension k L D X) (n:ℕ) (s:Γ(tensorPower X.space q58 n,⊤)):Γ(openPower k L D n,⊤) :=
  res _ (by simp) ((q67 X.inclusion q58 (openHodge k L D)
    H.onOpen n).hom.app _ (q10 X.inclusion s))
eN 2
rC
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by sorry
end ArithmeticThetaPalomarComponent485
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem compactComponent._proof_1 (x : X.space) : IsOpen (irreducibleComponent x) := by sorry
def compactComponent (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, compactComponent._proof_1 k L D X x⟩
end ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
namespace ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
abbrev componentOpen : X.space.Opens :=
  ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x
abbrev Component : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
abbrev projection : Component k L D X x ⟶ Spec (CommRingCat.of k) :=
  inclusion k L D X x ≫ X.projection
theorem componentIntegral : IsIntegral (Component k L D X x) := by sorry
attribute [instance] componentIntegral
theorem componentLocallyNoetherian : IsLocallyNoetherian (Component k L D X x) := by sorry
attribute [instance] componentLocallyNoetherian
def cuspSet : Set (Component k L D X x) :=
  {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps := {y : Component k L D X x // y ∈ cuspSet k L D X x}
abbrev hodge (H : Extension k L D X) : (Component k L D X x).Modules :=
  (Scheme.Modules.pullback (inclusion k L D X x)).obj H.line
abbrev power (H : Extension k L D X) (n : ℕ) : (Component k L D X x).Modules :=
  tensorPower (Component k L D X x) (hodge k L D X x H) n
end ArithmeticThetaComponentDegreeR0184
namespace ArithmeticThetaLineRoot
structure LocalFrame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) where
  equiv (V : X.Opens) (hVU : V ≤ U) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(H, V)
  naturality (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (a : Γ(X, V)) :
    H.presheaf.map (homOfLE hWV).op (equiv V hVU a) =
      equiv W (hWV.trans hVU) (X.presheaf.map (homOfLE hWV).op a)
variable (X : Scheme.{u}) [IsIntegral X]
structure NormalFrameCover (H : X.Modules) (ι : Type v) where
  opens : ι → X.Opens
  covers : (⊤ : X.Opens) ≤ iSup opens
  nonempty : ∀ i, Nonempty (opens i)
  affine : ∀ i, IsAffineOpen (opens i)
  normal : ∀ i, IsIntegrallyClosed Γ(X, opens i)
  frame : ∀ i, LocalFrame X H (opens i)
instance {X : Scheme.{u}} {H : X.Modules} {ι : Type v} (C : NormalFrameCover X H ι) (i : ι) : Nonempty (C.opens i) := C.nonempty i
end ArithmeticThetaLineRoot
namespace ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot
def sectionCoordinate (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U) (s : Γ(H, ⊤)) : Γ(X,U) :=
  (e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)
def sectionCoefficient (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (s : Γ(H, ⊤)) : X.functionField :=
  X.germToFunctionField U (sectionCoordinate X H U e s)
end ArithmeticThetaNormalizedSections
namespace ArithmeticThetaSectionOrder
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
def localOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules) {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i : ι) (x : X) : ℤ :=
  Scheme.ord (sectionCoefficient X H (C.opens i) (C.frame i) s) x
def MatchesSectionOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules) {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (D : X →₀ ℤ) : Prop :=
  ∀ (i : ι) (x : X), x ∈ C.opens i → D x = localOrder X H C s i x
end ArithmeticThetaSectionOrder
rC
namespace ArithmeticThetaPalomarD2_509.NormalizedSections
open ArithmeticThetaTensorPower
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) := (ArithmeticThetaPalomarHalf505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens)) (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
end ArithmeticThetaPalomarD2_509.NormalizedSections
namespace ArithmeticThetaPalomarD2_509.ComponentDegree
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)
def restrict (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(power k L D X x H n, ⊤) := ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection (inclusion k L D X x) H.line n s
def IsCompactD2 (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop := ∃ d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤), ArithmeticThetaPalomarD2_509.OpenHodge.IsD2 D.atlas.descent.family d ∧ ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k L H 24 s = ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k L 24 d
end ArithmeticThetaPalomarD2_509.ComponentDegree
rC
namespace ArithmeticThetaLineRoot
variable (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
def localFrameOfIso (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ SheafOfModules.over H U) : LocalFrame X H U where
  equiv V hVU :=
    (CategoryTheory.Iso.toLinearEquiv
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE hVU)))).mapIso e))
  naturality V W hWV hVU a := by
    let f : Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU) :=
      Over.homMk (homOfLE hWV)
    exact (PresheafOfModules.naturality_apply e.hom.val f.op a).symm
end ArithmeticThetaLineRoot
namespace ArithmeticThetaSheafTensor
open ArithmeticThetaLineRoot
variable (X : Scheme.{u}) (H K : X.Modules) (U : X.Opens)
def presheafOver : X.PresheafOfModules ⥤ PresheafOfModules.{u} (X.ringCatSheaf.over U).obj := PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj
def tensorFramePreIso (e : LocalFrame X H U) (f : LocalFrame X K U) : (SheafOfModules.unit (X.ringCatSheaf.over U)).val ≅ (presheafOver X U).obj (tensorPresheaf X H K) :=
  PresheafOfModules.isoMk
    (fun V ↦ ((TensorProduct.lid Γ(X, V.unop.left) Γ(X, V.unop.left)).symm.trans
      (TensorProduct.congr (e.equiv _ V.unop.hom.le) (f.equiv _ V.unop.hom.le))).toModuleIso)
    (fun {V W} g ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change (e.equiv W.unop.left W.unop.hom.le) 1 ⊗ₜ[Γ(X, W.unop.left)]
          (f.equiv W.unop.left W.unop.hom.le)
            (X.presheaf.map g.unop.left.op a) =
        H.presheaf.map g.unop.left.op (e.equiv V.unop.left V.unop.hom.le 1) ⊗ₜ[Γ(X, W.unop.left)]
          K.presheaf.map g.unop.left.op (f.equiv V.unop.left V.unop.hom.le a)
      rw [show g.unop.left = homOfLE g.unop.left.le from Subsingleton.elim _ _,
        e.naturality, f.naturality,
        (X.presheaf.map (homOfLE g.unop.left.le).op).hom.map_one])
def localTensorTrivializationHom (e : LocalFrame X H U) (f : LocalFrame X K U) : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ SheafOfModules.over (sheafTensor X H K) U := ⟨(tensorFramePreIso X H K U e f).hom ≫ (presheafOver X U).map (tensorUnitMap X H K)⟩
theorem localTensorTrivializationHom_isIso (e : LocalFrame X H U) (f : LocalFrame X K U) : IsIso (localTensorTrivializationHom X H K U e f) := by sorry
def localTensorTrivialization (e : LocalFrame X H U) (f : LocalFrame X K U) : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ SheafOfModules.over (sheafTensor X H K) U :=
  have := localTensorTrivializationHom_isIso X H K U e f
  asIso (localTensorTrivializationHom X H K U e f)
def tensorFrame (e : LocalFrame X H U) (f : LocalFrame X K U) : LocalFrame X (sheafTensor X H K) U := localFrameOfIso X (sheafTensor X H K) U (localTensorTrivialization X H K U e f)
end ArithmeticThetaSheafTensor
namespace ArithmeticThetaTensorPower
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor
def unitFrame (X : Scheme.{u}) (U : X.Opens) : LocalFrame X (SheafOfModules.unit X.ringCatSheaf) U where
  equiv V _ := LinearEquiv.refl Γ(X, V) Γ(X, V)
  naturality _ _ _ _ _ := rfl
run_cmd do
  let n := `ArithmeticThetaTensorPower.tensorPower.match_1
  let some (.defnInfo ci) := (← Lean.getEnv).find? n | throwError "Missing original tensorPower matcher"
  let key : Lean.Meta.Match.MatcherKey := { value := ci.value, compile := true, isPrivate := false }
  Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.modifyState env fun s => s.insert key n
def tensorPowerFrame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U) : (n : ℕ) → LocalFrame X (tensorPower X H n) U | 0 => unitFrame X U | n + 1 => tensorFrame X (tensorPower X H n) H U (tensorPowerFrame X H U e n) e
end ArithmeticThetaTensorPower
namespace ArithmeticThetaRootTorsor
rC
def IsGeneratingSection (X : Scheme.{u}) (M : X.Modules) (s : Γ(M, ⊤)) : Prop := ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (e : ArithmeticThetaLineRoot.LocalFrame X M U), IsUnit ((e.equiv U le_rfl).symm (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s))
end ArithmeticThetaRootTorsor
namespace ArithmeticThetaDiscriminant
noncomputable def partialEuler {R : Type*} [CommRing R] (a : R) (N : ℕ) : PowerSeries R := ∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (j + 1))
noncomputable def euler {R : Type*} [CommRing R] (a : R) : PowerSeries R := PowerSeries.mk (fun d => PowerSeries.coeff d (partialEuler a d))
noncomputable def P : PowerSeries ℚ := euler 1
end ArithmeticThetaDiscriminant
namespace ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
structure DivisorLine (Z : Scheme) where
  line : Z.Modules
  section_ : Γ(line, ⊤)
def Represents (Z : Scheme) [IsIntegral Z] [IsLocallyNoetherian Z] (A : DivisorLine Z) (E : Z →₀ ℤ) : Prop := Scheme.Modules.IsInvertible A.line ∧ A.section_ ≠ 0 ∧ (∃ ι : Type, Nonempty (NormalFrameCover Z A.line ι)) ∧ ∀ (ι : Type) (C : NormalFrameCover Z A.line ι), MatchesSectionOrder Z A.line C A.section_ E
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
def IsCuspHalfLine (A : DivisorLine (Component k L D X x)) : Prop := ∃ E : Component k L D X x →₀ ℤ, Represents (Component k L D X x) A E ∧ ∀ y, (y ∈ cuspSet k L D X x → E y = (L / 24 : ℕ)) ∧ (y ∉ cuspSet k L D X x → E y = 0)
def euler : PowerSeries k := PowerSeries.subst (PowerSeries.X ^ L) (PowerSeries.map (algebraMap ℚ k) ArithmeticThetaDiscriminant.P)
def diskHodgeIso (H : Extension k L D X) (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) : (Scheme.Modules.pullback f).obj (hodge k L D X x H) ≅ (Scheme.Modules.pullback V.disk).obj H.line := (Scheme.Modules.pullbackComp f (inclusion k L D X x)).app H.line ≪≫ (Scheme.Modules.pullbackCongr hf).app H.line
structure Twist (A : DivisorLine (Component k L D X x)) (H : Extension k L D X) where
  line : (Component k L D X x).Modules
  multiply : sheafTensor (Component k L D X x) line
      (tensorPower (Component k L D X x) A.line 2) ≅ hodge k L D X x H
  section_ : Γ(tensorPower (Component k L D X x) line 24, ⊤)
end ArithmeticThetaCommonHalfHodgeR0185
namespace ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171
def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv v
end ArithmeticThetaOpenHodgeR0180
namespace ArithmeticThetaPalomarTwist510
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)
def IsTwist {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (s : Γ(tensorPower X.space H.line 24, ⊤)) (W : Twist k L D X x A H) : Prop := Scheme.Modules.IsInvertible W.line ∧ ArithmeticThetaRootTorsor.IsGeneratingSection (Component k L D X x) (tensorPower (Component k L D X x) W.line 24) W.section_ ∧
  ∀ (U : (Component k L D X x).Opens) (μ : LocalFrame (Component k L D X x) W.line U), (power k L D X x H 24).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (ArithmeticThetaPalomarD2_509.ComponentDegree.restrict k L D X x H 24 s) = sectionCoordinate (Component k L D X x) (tensorPower (Component k L D X x) W.line 24) U (tensorPowerFrame (Component k L D X x) W.line U μ 24) W.section_ •
      tensorPowerSection (Component k L D X x) (hodge k L D X x H) 24 U (W.multiply.hom.app U (tensorSection (Component k L D X x) W.line (tensorPower (Component k L D X x) A.line 2) U (μ.equiv U le_rfl 1) (tensorPowerSection (Component k L D X x) A.line 2 U (A.line.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op A.section_))))
def pullMultiply {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (W : Twist k L D X x A H) {Z : Scheme} (f : Z ⟶ Component k L D X x) : sheafTensor Z ((Scheme.Modules.pullback f).obj W.line) (tensorPower Z ((Scheme.Modules.pullback f).obj A.line) 2) ≅ (Scheme.Modules.pullback f).obj (hodge k L D X x H) :=
  sheafTensorCongr Z (Iso.refl _) (ArithmeticThetaPalomarHalf505.powerComparison Z _ f A.line 2).symm ≪≫ (ArithmeticThetaPalomarHalf505.binary f W.line (tensorPower _ A.line 2)).symm ≪≫ (Scheme.Modules.pullback f).mapIso W.multiply
def IsTateRoot {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (W : Twist k L D X x A H) (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) (v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤)) : Prop := ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((Scheme.Modules.pullback f).obj W.line) ⊤ v ∧
  tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj W.line) 24 ⊤ v = ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection f W.line 24 W.section_ ∧ ∀ η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤), ExtendsGenerator k L H V η → (diskHodgeIso k L D X x H V f hf).hom.app ⊤ ((pullMultiply k L D X x W f).hom.app ⊤
        (tensorSection (Disk k) ((Scheme.Modules.pullback f).obj W.line) (tensorPower (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2) ⊤ v (tensorPowerSection (Disk k) ((Scheme.Modules.pullback f).obj A.line) 2 ⊤ (pullbackGlobalSection f A.line A.section_)))) = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (euler k L ^ 2 * PowerSeries.X ^ (L / 12)) • η
end ArithmeticThetaPalomarTwist510
namespace ArithmeticThetaPalomarTwist510
theorem discriminantTwistUnit : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPalomarD2_509.ComponentDegree.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∃ W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H, ArithmeticThetaPalomarTwist510.IsTwist k L D X x s W := by sorry
end ArithmeticThetaPalomarTwist510
namespace ArithmeticThetaPalomarTwist510
theorem discriminantTateRoot : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPalomarD2_509.ComponentDegree.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∀ (W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H), ArithmeticThetaPalomarTwist510.IsTwist k L D X x s W → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (hf : CategoryTheory.CategoryStruct.comp f (ArithmeticThetaComponentDegreeR0184.inclusion k L D X x) = V.disk), ∃! v : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPalomarTwist510.IsTateRoot k L D X x W V f hf v := by sorry
end ArithmeticThetaPalomarTwist510
