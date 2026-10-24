module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section elab "mX" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
macro "rc":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {})
noncomputable section
universe u v
open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z8, SheafOfModules → z9, CommRingCat → z10, LinearMap → z11, ModuleCat → z12, AddMonoidHom → z13, RingHom → z14, IsDomain → z15, IsIntegrallyClosed → z16, IsNoetherianRing → z17, IsAlgClosed → z18, Finsupp → z19, SetLike → z20, Submodule → z21, FractionRing → z22, HomogeneousIdeal → z23, HomogeneousLocalization → z24, IsUnit → z25, IsScalarTower → z26, AddSubgroupClass → z27, AddSubmonoidClass → z28, Algebra → z29, Nonempty → z30
open CategoryTheory renaming MonoidalCategory → z7
open AlgebraicGeometry renaming Scheme → zS
open AlgebraicGeometry.Scheme.Modules renaming pullback → zPB, pullbackComp → zPC, pullbackPushforwardAdjunction → zPA, pushforward → zPF open CommRingCat renaming of → zCR, ofHom → zCH open Ideal.Quotient renaming mk → zQM open PresheafOfModules renaming sheafificationAdjunction → zSA, sheafification → zSF open WeierstrassCurve renaming Projective → zWP open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DirectSum HomogeneousLocalization MonoidalCategory MvPolynomial Opposite TopologicalSpace
set_option hygiene false
set_option quotPrecheck false
local notation "T0(" X ")"=> (@AlgebraicGeometry.PresheafedSpace.carrier z10 z10.instCategory (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace z10 z10.instCategory (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) local notation "T2"=> (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
local notation "T7"=> (@z19 T2 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) local notation "T8(" R "," inst ")"=> (@CommSemiring.toSemiring R (@z0.toCommSemiring R inst))
local notation "T20(" R "," inst ")"=> (@AddMonoidAlgebra.instAddCommMonoid R T7 T8(R,inst)) local notation "T17(" R "," inst ")"=> (@AddMonoidAlgebra.instModule R R T7 T8(R,inst) T8(R,inst) (@Semiring.toModule R T8(R,inst)))
local notation "T5(" R "," inst ")"=> (@z6 T2 R (@z0.toCommSemiring R inst)) local notation "T28(" R "," inst ")"=> (@z21 R T5(R,inst) T8(R,inst) T20(R,inst) T17(R,inst))
local notation "T11"=> (@z19.instAddMonoid T2 Nat Nat.instAddMonoid) local notation "T22(" R "," inst ")"=> (@AddMonoidAlgebra.semiring R T7 T8(R,inst) T11)
local notation "T24(" R "," inst ")"=> (@z21.setLike R T5(R,inst) T8(R,inst) T20(R,inst) T17(R,inst)) local notation "T1(" R "," W "," inst ")"=> (@z23.toIdeal Nat T28(R,inst) T5(R,inst) T22(R,inst) T24(R,inst) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1 R inst) (@z6.homogeneousSubmodule T2 R (@z0.toCommSemiring R inst)) instDecidableEqNat Nat.instAddMonoid (@z6.gradedAlgebra T2 R (@z0.toCommSemiring R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR R inst (@z3.toProjective R W)))
local notation "T9(" X ")"=> (@TopologicalSpace.Opens (TopCat.carrier T0(X)) (TopCat.str T0(X))) local notation "T6(" X ")"=> (@Preorder.smallCategory T9(X) (@PartialOrder.toPreorder T9(X) (@TopologicalSpace.Opens.instPartialOrder (TopCat.carrier T0(X)) (TopCat.str T0(X)))))
local notation "T13(" X ")"=> (@CategoryTheory.Functor (Opposite T9(X)) (@CategoryTheory.Category.opposite T9(X) T6(X)) RingCat RingCat.instCategory) local notation "T18(" X ")"=> (@CategoryTheory.Functor.category (Opposite T9(X)) (@CategoryTheory.Category.opposite T9(X) T6(X)) RingCat RingCat.instCategory)
local notation "T19(" X ")"=> (@Opens.grothendieckTopology (TopCat.carrier T0(X)) (TopCat.str T0(X))) local notation "T3(" X ")"=> (@CategoryTheory.ObjectProperty.FullSubcategory.obj T13(X) T18(X) (@CategoryTheory.Presheaf.IsSheaf T9(X) T6(X) RingCat RingCat.instCategory T19(X)) (AlgebraicGeometry.Scheme.ringCatSheaf X))
local notation "T16(" R "," inst ")"=> (@z29.toSMul R T5(R,inst) (@z0.toCommSemiring R inst) T22(R,inst) (@AddMonoidAlgebra.algebra R R T7 (@z0.toCommSemiring R inst) T8(R,inst) (@z29.id R (@z0.toCommSemiring R inst)) T11)) local notation "T32(" R "," inst ")"=> (@AddMonoidAlgebra.ring R T7 (@z0.toRing R inst) T11)
local notation "T4(" R "," W "," inst ")"=> (@z21.Quotient.module' T5(R,inst) T5(R,inst) T32(R,inst) (@AddMonoidAlgebra.addCommGroup R T7 (@z0.toRing R inst)) (@Semiring.toModule T5(R,inst) T22(R,inst)) R T8(R,inst) T16(R,inst) (@z6.instModuleSelf T2 R inst) (@WeierstrassProjModel.kw_lrComul_tensorProj._proof_1 R inst) T1(R,W,inst)) local notation "T21(" R "," inst ")"=> (@AddMonoidAlgebra.commRing R T7 inst (@z19.instAddCommMonoid T2 Nat Nat.instAddCommMonoid))
local notation "T10(" R "," W "," inst ")"=> (@z21.Quotient.addCommGroup T5(R,inst) T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst)) (@Ring.toAddCommGroup T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst))) (@Semiring.toModule T5(R,inst) (@Ring.toSemiring T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst)))) T1(R,W,inst)) local notation "T12(" R "," W "," inst ")"=> (@WeierstrassProjModel.ProjModelRingCR R inst (@z3.toProjective R W))
local notation "T14(" R "," W "," inst ")"=> (@z21.Quotient.addCommGroup T5(R,inst) T5(R,inst) T32(R,inst) (@AddMonoidAlgebra.addCommGroup R T7 (@z0.toRing R inst)) (@Semiring.toModule T5(R,inst) T22(R,inst)) T1(R,W,inst)) local notation "T15(" R "," inst ")"=> (@Ring.toSemiring T5(R,inst) T32(R,inst))
local notation "T23(" R "," inst ")"=> (@OfNat.ofNat R (nat_lit 0) (@Zero.toOfNat0 R (@MulZeroClass.toZero R (@instMulZeroClassOfSemiring R T8(R,inst))))) local notation "T25(" X ")"=> (@CategoryTheory.CategoryStruct.id T13(X) (@CategoryTheory.Category.toCategoryStruct T13(X) T18(X)) T3(X))
local notation "T26"=> (@Semiring.toNonAssocSemiring (RingCat.carrier S) (@Ring.toSemiring (RingCat.carrier S) (RingCat.ring S))) local notation "T27"=> (@Semiring.toNonAssocSemiring (RingCat.carrier Y) (@Ring.toSemiring (RingCat.carrier Y) (RingCat.ring Y)))
local notation "T29(" R ")"=> (@Semiring.toNonAssocSemiring (RingCat.carrier R) (@Ring.toSemiring (RingCat.carrier R) (RingCat.ring R))) local notation "T30(" X ")"=> (@Semiring.toNonAssocSemiring (RingCat.carrier X) (@Ring.toSemiring (RingCat.carrier X) (RingCat.ring X)))
local notation "T31(" R "," W "," inst ")"=> (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace (@ArithmeticThetaRelativeKatoR0169.Curve R inst W)))
set_option quotPrecheck true
set_option hygiene true
set_option hygiene false
set_option quotPrecheck false
local notation "q0"=>(TopCat.carrier.{0} (@AlgebraicGeometry.PresheafedSpace.carrier.{0,1,0} z10.{0} z10.instCategory.{0} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,0,0} z10.{0} z10.instCategory.{0} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} (@Compactification.space.{0} k inst L D X)))))) local notation "q1"=>(Compactification k L D)
local notation "q2"=>(algebraMap (z4 k) (z5 k)) local notation "q3"=>((@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1,0,0} z10.{0} z10.instCategory.{0} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{0} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{0} (@Compactification.space.{0} k inst L D X)))))
local notation "q4"=>((V.disk (closedPoint k))) local notation "q5"=>((Component k L D X x))
local notation "q6"=>((canonicalDivisorData k L D X x divisor effective normal)) local notation "q7"=>((𝟙 X.ringCatSheaf.obj))
local notation "q8"=>((algebraMap R (z22 R))) local notation "q9"=>(Curve (z5 k) (TateCurve k L))
local notation "q10"=>((@Ring.toSemiring.{u_1} R (@z0.toRing.{u_1} R inst))) local notation "q11"=>(Spec.map (zCH (algebraMap A B)))
local notation "q12"=>(Compactification k (level N) D) local notation "q13"=>(IsLocallyNoetherian X)
local notation "q14"=>(projModelGradingCR W.toProjective) local notation "q15"=>((@z0.toCommSemiring.{u_1} R inst))
local notation "q16"=>((AddCommGrpCat.carrier.{u_1} x2)) local notation "q17"=>((AddCommGrpCat.carrier.{u_1} x1))
local notation "q18"=>((AddCommGrpCat.carrier.{u_1} Y)) local notation "q19"=>((AddCommGrpCat.carrier.{u_1} X))
local notation "q20"=>(ArithmeticThetaRelativeDiscriminantR0171.Base R) local notation "q21"=>((universalFamily k L A))
local notation "q22"=>(preDecompose 𝒜 I ℬ hmem a) local notation "q23"=>(Extension k (level N) D X)
local notation "q24"=>(z9.unit X.ringCatSheaf) local notation "q25"=>(DiskTest k (level N) D X)
local notation "q26"=>(((zPB C.map).obj J.line)) local notation "q27"=>(LevelData k (level N))
local notation "q28"=>(quotGradingSubmodule 𝒜 I) local notation "q29"=>((zPB V.disk).obj H.line)
local notation "q30"=>((Component k (level N) D X q4)) local notation "q31"=>(ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring)
local notation "q32"=>(z6 (Fin 3) R) local notation "q33"=>(Hodge (z5 k) (TateCurve k L))
local notation "q34"=>(inclusion k (level N) D X q4) local notation "q35"=>((P544.idealModule E.zero.ker))
local notation "q36"=>(@z14.instFunLike.{u_1,u_1} (RingCat.carrier.{u_1} X) (RingCat.carrier.{u_1} Y) T30(X) T27) local notation "q37"=>(IsIntegral (Curve R W))
local notation "q38"=>((inclusion≫A.level.projection)) local notation "q39"=>((z6.homogeneousSubmodule (Fin N) S))
local notation "q40"=>(IsLocallyNoetherian (Curve R W)) local notation "q41"=>(pieceHom 𝒜 I ℬ hmem)
local notation "q42"=>(gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))) local notation "q43"=>(z3.{u_1} R)
local notation "q44"=>(ArithmeticThetaLocalWeierstrassR0203.Base l) local notation "q45"=>(ArithmeticThetaLocalWeierstrassR0203.Base k)
local notation "q46"=>(@z14.{u_1,u_1} (RingCat.carrier.{u_1} R) (RingCat.carrier.{u_1} S) T29(R) T26) local notation "q47"=>((hodge D.atlas.descent.family))
local notation "q48"=>((Curve R W).presheaf.obj (Opposite.op U.1)) local notation "q49"=>(IsIntegral (GenericCurve R W))
local notation "q50"=>((zPB T.disk).obj H.line) local notation "q51"=>((Curve R W).presheaf.obj (Opposite.op U))
local notation "q52"=>((baseMap S R C.scalar)) local notation "q53"=>((z9.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom))
local notation "q54"=>((Base A.quotient.ring)) local notation "q55"=>(IsLocallyNoetherian (GenericCurve R W))
local notation "q56"=>(tensorPower X.space H.line (weight N)) local notation "q57"=>(schemeHomOverComp ψ hψ x)
local notation "q58"=>(ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (𝟙 (Base R))) local notation "q59"=>((zS.ΓSpecIso (zCR A)))
local notation "q60"=>((Classical.choice hV.down)) local notation "q61"=>(schemeHomOverComp ψ hψ (mul t x y))
local notation "q62"=>(J.presheaf.map (homOfLE (show p ⁻¹ᵁ U≤⊤ from le_top)).op t) local notation "q63"=>(ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ)
local notation "q64"=>((@AddCommGroup.toAddCommMonoid.{u_1} T12(R,W,inst) T14(R,W,inst))) local notation "q65"=>((@AddCommGroup.toAddCommMonoid.{u_1} T12(R,W,inst) T10(R,W,inst)))
local notation "q66"=>(SchemeHomOver t (structureMap R W)) local notation "q67"=>((@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
local notation "q68"=>((@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
set_option quotPrecheck true
set_option hygiene true
section rc
abbrev NeronModelInfra.SchemeHomOver{B Y X:Scheme.{u}}(g:Y⟶B)(f:X⟶B):={φ:Y⟶X//φ≫f=g} end
open NeronModelInfra open NeronModelInfra renaming SchemeHomOver → sh namespace HomogeneousIdealQuotientGrading rc
section Engine
variable {ι A σ τ:Type*} variable [z0 A] [z20 σ A] [z28 σ A] (𝒜:ι→ σ) variable (I:Ideal A) variable [z20 τ (A ⧸ I)] [z28 τ (A ⧸ I)] (ℬ:ι→ τ)
def pieceHom(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(i:ι):𝒜 i→+ℬ i:=z13.codRestrict ((zQM I).toAddMonoidHom.comp (z28.subtype (𝒜 i))) (ℬ i) (fun a=> hmem i a a.2)
@[simp] lemma pieceHom_coe(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(i:ι)(a:𝒜 i):(q41 i a:A ⧸ I)=zQM I (a:A):=by sorry
omit [z28 σ A] [z28 τ (A ⧸ I)] in
theorem gradedMonoidOfImages[AddMonoid ι][z20.GradedMonoid 𝒜](hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hsurj:∀ (i:ι),∀ b∈ℬ i,∃ a∈𝒜 i,zQM I a=b):z20.GradedMonoid ℬ:=by sorry
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(y:⨁ i,𝒜 i):DirectSum.coeAddMonoidHom ℬ (DirectSum.map (q41) y)=zQM I (DirectSum.coeAddMonoidHom 𝒜 y):=by sorry
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i):A→+⨁ i,ℬ i:=(DirectSum.map (q41)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_apply(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(a:A):q22=DirectSum.map (q41) (decompose 𝒜 a):=rfl
lemma preDecompose_apply_apply(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(a:A)(i:ι):q22 i=q41 i (decompose 𝒜 a i):=by
  rw [preDecompose_apply,DirectSum.map_apply]
lemma preDecompose_of_mem(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i){i:ι}{a:A}(ha:a∈𝒜 i):q22=DirectSum.of (fun j=> ℬ j) i ⟨zQM I a,hmem i a ha⟩:=by sorry
lemma coeAddMonoidHom_preDecompose(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(a:A):DirectSum.coeAddMonoidHom ℬ (q22)=zQM I a:=by sorry
lemma preDecompose_eq_zero_of_mem(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hI:I.IsHomogeneous 𝒜){a:A}(ha:a∈I):q22=0:=by sorry
def quotDecompose(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hI:I.IsHomogeneous 𝒜):A ⧸ I→+⨁ i,ℬ i:=QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem) (fun _ ha=> preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
@[simp] lemma quotDecompose_mk(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hI:I.IsHomogeneous 𝒜)(a:A):quotDecompose 𝒜 I ℬ hmem hI (zQM I a)=q22:=by sorry
@[reducible] def decompositionOfImages(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hsurj:∀ (i:ι),∀ b∈ℬ i,∃ a∈𝒜 i,zQM I a=b)(hI:I.IsHomogeneous 𝒜):DirectSum.Decomposition ℬ:=
  DirectSum.Decomposition.ofAddHom ℬ (quotDecompose 𝒜 I ℬ hmem hI)
    (by
      refine z13.ext fun x=> ?_
      obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
      rw [z13.comp_apply,z13.id_apply,quotDecompose_mk,
        coeAddMonoidHom_preDecompose])
    (by
      refine DirectSum.addHom_ext fun i b=> ?_
      rw [z13.comp_apply,z13.id_apply,DirectSum.coeAddMonoidHom_of]
      obtain ⟨a,ha,hab⟩:=hsurj i (b:A ⧸ I) b.2
      rw [← hab,quotDecompose_mk,preDecompose_of_mem 𝒜 I ℬ hmem ha]
      exact congrArg _ (Subtype.ext hab))
@[reducible] def gradedRingOfImages(hmem:∀ (i:ι) (a:A),a∈𝒜 i→ zQM I a∈ℬ i)(hsurj:∀ (i:ι),∀ b∈ℬ i,∃ a∈𝒜 i,zQM I a=b)(hI:I.IsHomogeneous 𝒜):GradedRing ℬ where
  toGradedMonoid:=gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition:=decompositionOfImages 𝒜 I ℬ hmem hsurj hI
end Engine
section SubmoduleVersion
variable {ι R A:Type*} variable [z0 R] [z0 A] [z29 R A] variable (𝒜:ι→ z21 R A) variable (I:Ideal A)
def quotGradingSubmodule(i:ι):z21 R (A ⧸ I):=(𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff{i:ι}{x:A ⧸ I}:x∈q28 i↔∃ a∈𝒜 i,zQM I a=x:=by sorry
lemma mk_mem_quotGradingSubmodule{i:ι}{a:A}(ha:a∈𝒜 i):zQM I a∈q28 i:=(mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a,ha,rfl⟩
instance quotGradingSubmoduleGradedMonoid[AddMonoid ι][z20.GradedMonoid 𝒜]:z20.GradedMonoid (q28):=by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra(hI:I.IsHomogeneous 𝒜):GradedAlgebra (q28):=gradedRingOfImages 𝒜 I (q28) (fun _ _ ha=> mk_mem_quotGradingSubmodule 𝒜 I ha) (fun _ _ hb=> (mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous(J:z23 𝒜):GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal):=quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
end SubmoduleVersion
end HomogeneousIdealQuotientGrading open HomogeneousIdealQuotientGrading
section rc variable {F:Type*} [z0 F]
theorem ProjWeierstrassCubicPrime.isHomogeneous_polynomial(V:zWP F):V.polynomial.IsHomogeneous 3:=by sorry end
open ProjWeierstrassCubicPrime namespace WeierstrassProjModel rc
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R:Type*} [z0 R]
theorem span_polynomial_isHomogeneousCR(V:zWP R):(Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R):=by sorry
def projModelHomogeneousIdealCR(V:zWP R):z23 (homogeneousSubmodule (Fin 3) R):=⟨Ideal.span {V.polynomial},span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal(V:zWP R):(projModelHomogeneousIdealCR V).toIdeal=Ideal.span {V.polynomial}:=rfl
abbrev ProjModelRingCR(V:zWP R):Type _:=q32 ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR(V:zWP R):ℕ→ z21 R (ProjModelRingCR V):=quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR(V:zWP R):zS:=Proj (projModelGradingCR V)
def projModelStrCR(V:zWP R):Proj (projModelGradingCR V)⟶Spec (zCR R):=Proj.toSpecZero (projModelGradingCR V)≫Spec.map (zCH (algebraMap R ((projModelGradingCR V) 0)))
end Carrier variable (R:Type u) [CommRing R]
section ZeroSection
variable (W:z3 R)
open MvPolynomial in
theorem kw_mk_X1_mem_one_CR:zQM (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 1:q32)∈q14 1:=mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
theorem kw_lrComul_tensorProj._proof_1.{u_1}:∀ {R:Type u_1} [inst:z0.{u_1} R],@z26.{u_1,u_1,u_1} R T5(R,inst) T5(R,inst) T16(R,inst) (@instSMulOfMul.{u_1} T5(R,inst) (@Distrib.toMul.{u_1} T5(R,inst) (@instDistribOfSemiring.{u_1} T5(R,inst) T22(R,inst)))) T16(R,inst):=by sorry
theorem kw_lrChart_aux._proof_1.{u_1}:∀ {R:Type u_1} [inst:z0.{u_1} R] (W:q43),@z27.{u_1,u_1} (@z21.{u_1,u_1} R T12(R,W,inst) q10 q64 T4(R,W,inst)) T12(R,W,inst) (@AddGroup.toSubNegMonoid.{u_1} T12(R,W,inst) (@AddCommGroup.toAddGroup.{u_1} T12(R,W,inst) T14(R,W,inst))) (@z21.setLike.{u_1,u_1} R T12(R,W,inst) q10 q64 T4(R,W,inst)):=by sorry
theorem kw_lrChart_aux._proof_2.{u_1}:∀ {R:Type u_1} [inst:z0.{u_1} R] (W:q43),@z27.{u_1,u_1} (@z21.{u_1,u_1} R T12(R,W,inst) q10 q65 T4(R,W,inst)) T12(R,W,inst) (@AddGroup.toSubNegMonoid.{u_1} T12(R,W,inst) (@AddCommGroup.toAddGroup.{u_1} T12(R,W,inst) T10(R,W,inst))) (@z21.setLike.{u_1,u_1} R T12(R,W,inst) q10 q65 T4(R,W,inst)):=by sorry
theorem kw_lrSixU_toE._proof_1:@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (@One.toOfNat1.{0} Nat Nat.instOne)):=by sorry
theorem kw_lrAdd_comulHom._proof_2.{u_1}:∀ {R:Type u_1} [inst:z0.{u_1} R],@z28.{u_1,u_1} T28(R,inst) T5(R,inst) (@AddMonoid.toAddZeroClass.{u_1} T5(R,inst) (@AddCommMonoid.toAddMonoid.{u_1} T5(R,inst) T20(R,inst))) T24(R,inst):=by sorry
theorem kw_lrAdd_comulHom._proof_3.{u_1}:∀ {R:Type u_1} [inst:z0.{u_1} R] (W:q43),@Ideal.IsTwoSided.{u_1} T5(R,inst) (@CommSemiring.toSemiring.{u_1} T5(R,inst) (@z0.toCommSemiring.{u_1} T5(R,inst) T21(R,inst))) (@z23.toIdeal.{0,u_1,u_1} Nat T28(R,inst) T5(R,inst) T22(R,inst) T24(R,inst) (@WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} R inst) (@z6.homogeneousSubmodule.{0,u_1} T2 R q15) instDecidableEqNat Nat.instAddMonoid (@z6.gradedAlgebra.{0,u_1} T2 R q15) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@z3.toProjective.{u_1} R W))):=by sorry
theorem kw_lrAddNegDiag_negSubstGen._proof_1:@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q67 q68):=by sorry
theorem kwYEvalRingHom._proof_2.{u_1}:∀ (R:Type u_1) [inst:z0.{u_1} R] (W:q43) (a:@z6.{0,u_1} T2 R q15) (ha:@Membership.mem.{u_1,u_1} T5(R,inst) (@Ideal.{u_1} T5(R,inst) T15(R,inst)) (@z20.instMembership.{u_1,u_1} (@Ideal.{u_1} T5(R,inst) T15(R,inst)) T5(R,inst) (@z21.setLike.{u_1,u_1} T5(R,inst) T5(R,inst) T15(R,inst) (@Semiring.toAddCommMonoid.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toModule.{u_1} T5(R,inst) T15(R,inst)))) T1(R,W,inst) a),@Eq.{u_1+1} R (@DFunLike.coe.{u_1+1,u_1+1,u_1+1} (@z14.{u_1,u_1} T5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R T8(R,inst))) T5(R,inst) (fun (x:@z6.{0,u_1} T2 R q15)=> R) (@z14.instFunLike.{u_1,u_1} T5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R T8(R,inst))) (@z6.eval.{u_1,0} R T2 q15 (@Matrix.vecCons.{u_1} R q67 T23(R,inst) (@Matrix.vecCons.{u_1} R q68 (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R (@AddGroupWithOne.toAddMonoidWithOne.{u_1} R (@Ring.toAddGroupWithOne.{u_1} R (@z0.toRing.{u_1} R inst)))))) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) T23(R,inst) (@Matrix.vecEmpty.{u_1} R))))) a) T23(R,inst):=by sorry
run_cmd do
  for n in [``kw_lrComul_tensorProj._proof_1,``kw_lrChart_aux._proof_1,``kw_lrChart_aux._proof_2,``kw_lrSixU_toE._proof_1,``kw_lrAdd_comulHom._proof_2,``kw_lrAdd_comulHom._proof_3,``kw_lrAddNegDiag_negSubstGen._proof_1,`WeierstrassProjModel.kwYEvalRingHom._proof_2] do
    let some ci:=(← Lean.getEnv).find? n | throwError "missing proof cache seed"
    Lean.modifyEnv fun env=> Lean.Meta.auxLemmasExt.modifyState env fun st=> { st with lemmas:=st.lemmas.insert { type:=ci.type,isPrivate:=false,defeq:=false } (n,ci.levelParams) }
open MvPolynomial in
def kwYEvalRingHom:ProjModelRingCR W.toProjective→+*R:=
  Ideal.Quotient.lift _ (z6.eval ![(0:R),1,0]) fun a ha=> by
    refine (Ideal.span_le.mpr ?_:Ideal.span _≤z14.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff,z20.mem_coe,z14.mem_ker]
    exact z3.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1:kwYEvalRingHom R W (zQM _ (X 1:q32))=1:=by sorry
def kwYChartEval:z24.Away (q14) (zQM _ (z6.X 1:q32))→+*R:=(IsLocalization.Away.lift (g:=kwYEvalRingHom R W) (zQM _ (z6.X 1:q32)) (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (z24.Away (q14) (zQM _ (z6.X 1:q32))) (Localization.Away (zQM (projModelHomogeneousIdealCR W.toProjective).toIdeal (z6.X 1:q32))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap:(kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective))=z14.id R:=by sorry
theorem kwYChartEval_section:(kwYChartEval R W).comp ((z24.fromZeroRingHom (q14) _).comp (algebraMap R (q14 0)))=z14.id R:=by sorry
def kwZeroSect:sh (𝟙 (Spec (zCR R))) (projModelStrCR W.toProjective):=
  ⟨Spec.map (zCH (kwYChartEval R W))≫
    Proj.awayι (q14) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR,Category.assoc]
    rw [← Category.assoc (Proj.awayι ..),Proj.awayι_toSpecZero,← Spec.map_comp,
      ← Spec.map_comp,← z10.ofHom_comp,← z10.ofHom_comp,
      kwYChartEval_section,z10.ofHom_id,Spec.map_id]⟩
end ZeroSection
def schemeHomOverComp{B T' T A:Scheme.{u}}{t:T⟶B}{t':T'⟶B}{f:A⟶B}(ψ:T'⟶T)(hψ:ψ≫t=t')(x:sh t f):sh t' f:=
  ⟨ψ≫x.1,by rw [Category.assoc,x.2,hψ]⟩
@[simp]
theorem schemeHomOverComp_coe{B T' T A:Scheme.{u}}{t:T⟶B}{t':T'⟶B}{f:A⟶B}(ψ:T'⟶T)(hψ:ψ≫t=t')(x:sh t f):(q57).1=ψ≫x.1:=rfl
structure RelativeGroupLaw(R:Type u)[z0 R]{A:zS.{u}}(f:A⟶Spec (zCR R)) where (mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f→ sh t f) (one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f) (inv:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f) (mul_assoc:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y z:sh t f),mul t (mul t x y) z=mul t x (mul t y z)) (one_mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (one t) x=x) (mul_one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t x (one t)=x) (inv_mul_cancel:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (inv t x) x=one t) (mul_natural:∀ {T T':zS.{u}} (t:T⟶Spec (zCR R)) (t':T'⟶Spec (zCR R)) (ψ:T'⟶T) (hψ:ψ≫t=t') (x y:sh t f),q61=mul t' (q57) (schemeHomOverComp ψ hψ y))
end WeierstrassProjModel open WeierstrassProjModel namespace ArithmeticThetaRelativeKatoR0169 rc variable (R:Type u) [z0 R]
abbrev Curve(W:z3 R):zS.{u}:=projModelCR W.toProjective
def structureMap(W:z3 R):Curve R W⟶Spec (zCR R):=projModelStrCR W.toProjective
def origin(W:z3 R):Spec (zCR R)⟶Curve R W:=(kwZeroSect R W).val
abbrev Law(W:z3 R):=WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw(W:z3 R)(G:Law R W):Prop:=(∀ {V:zS.{u}} (t:V⟶Spec (zCR R)),(G.one t).val=t≫origin R W)∧(∀ {V:zS.{u}} (t:V⟶Spec (zCR R)) (x y:q66),G.mul t x y=G.mul t y x)
end ArithmeticThetaRelativeKatoR0169 open ArithmeticThetaRelativeKatoR0169 
section rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
def WeierstrassProjModel.RelativeGroupLaw.nsmul(G:RelativeGroupLaw R f){T:zS.{u}}(t:T⟶Spec (zCR R))(n:ℕ)(x:sh t f):sh t f:=Nat.rec (G.one t) (fun _ ih=> G.mul t ih x) n end
namespace GoodReductionJacobian rc
def schemeHomOverComp{B T' T A:Scheme.{u}}{t:T⟶B}{t':T'⟶B}{f:A⟶B}(ψ:T'⟶T)(hψ:ψ≫t=t')(x:sh t f):sh t' f:=
  ⟨ψ≫x.1,by rw [Category.assoc,x.2,hψ]⟩
structure RelativeGroupLaw(R:Type u)[z0 R]{A:zS.{u}}(f:A⟶Spec (zCR R)) where (mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f→ sh t f) (one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f) (inv:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f) (mul_assoc:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y z:sh t f),mul t (mul t x y) z=mul t x (mul t y z)) (one_mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (one t) x=x) (mul_one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t x (one t)=x) (inv_mul_cancel:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (inv t x) x=one t) (mul_natural:∀ {T T':zS.{u}} (t:T⟶Spec (zCR R)) (t':T'⟶Spec (zCR R)) (ψ:T'⟶T) (hψ:ψ≫t=t') (x y:sh t f),q61=mul t' (q57) (schemeHomOverComp ψ hψ y))
section rc
def RelativeGroupLaw.IsCommutative{R:Type u}[z0 R]{A:zS.{u}}{f:A⟶Spec (zCR R)}(G:RelativeGroupLaw R f):Prop:=∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y:sh t f),G.mul t x y=G.mul t y x end
end GoodReductionJacobian namespace GoodReductionJacobian.RelativeGroupLaw rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
def nsmul(G:RelativeGroupLaw R f){T:zS.{u}}(t:T⟶Spec (zCR R))(n:ℕ)(x:sh t f):sh t f:=Nat.rec (G.one t) (fun _ ih=> G.mul t ih x) n
abbrev idPoint:sh f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul(G:RelativeGroupLaw R f)(n:ℕ):A⟶A:=(G.nsmul f n idPoint).1
end GoodReductionJacobian.RelativeGroupLaw
section rc
abbrev ArithmeticThetaRelativeDiscriminantR0171.Base(R:Type u)[z0 R]:=Spec (zCR R) end
open ArithmeticThetaRelativeDiscriminantR0171 namespace ArithmeticThetaFullLevelCoverR0175 rc variable (R:Type u) [z0 R] (W:z3 R) (G:Law R W)
structure FullLevel(L:ℕ){T:zS.{u}}(t:T⟶Base R) where (x:q66) (y:q66) (killed_x:G.nsmul t L x=G.one t) (killed_y:G.nsmul t L y=G.one t) (avoids:∀ i j:Fin L,i.val≠0∨j.val≠0→ Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val) (Set.range (origin R W)))
structure LevelScheme(L:ℕ) where (space:zS.{u}) (projection:space⟶Base R) (level:ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L projection)
def Represents{L:ℕ}(D:LevelScheme R W G L):Prop:=∀ (T:zS.{u}) (t:T⟶Base R) (A:ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L t),∃! q:sh t D.projection,q.val≫D.level.x.val=A.x.val∧q.val≫D.level.y.val=A.y.val
def levelDegree(L:ℕ):ℕ:=Nat.card ((ZMod L × ZMod L) ≃+(ZMod L × ZMod L))
end ArithmeticThetaFullLevelCoverR0175 open ArithmeticThetaFullLevelCoverR0175 namespace ArithmeticThetaLegendreAtlasR0176 rc
abbrev LegendreRing(k:Type u)[z1 k]:=Localization.Away (Polynomial.X*(Polynomial.X - 1):Polynomial k)
def parameter(k:Type u)[z1 k]:LegendreRing k:=algebraMap (Polynomial k) (LegendreRing k) Polynomial.X
def legendre(k:Type u)[z1 k]:z3 (LegendreRing k) where
  a₁:=0
  a₂:=-(parameter k+1)
  a₃:=0
  a₄:=parameter k
  a₆:=0
def legendreBaseMap(k:Type u)[z1 k]:Base (LegendreRing k)⟶Base k:=Spec.map (zCH (algebraMap k (LegendreRing k)))
structure SignAction(R:Type u)[z0 R](W:z3 R)(G:Law R W){L:ℕ}(Z:LevelScheme R W G L) where (map:Z.space⟶Z.space) (over_eq:map≫Z.projection=Z.projection) (square:map≫map=𝟙 _) (x_eq:map≫Z.level.x.val=(G.inv Z.projection Z.level.x).val) (y_eq:map≫Z.level.y.val=(G.inv Z.projection Z.level.y).val) (free:IsEmpty (equalizer map (𝟙 Z.space):zS.{u}))
structure SignQuotient(k:Type u)[z1 k]{X:zS.{u}}(p:X⟶Base k)(σ:X⟶X) where (ring:Type u) [commRing:z0 ring] [algebra:z29 k ring] (q:X⟶Base ring) (over_eq:q≫Spec.map (zCH (algebraMap k ring))=p) (invariant:σ≫q=q) (finite:IsFinite q) (etale:Etale q) (surjective:Surjective q) (degree:∀ x,q.finrank x=2) (smooth:SmoothOfRelativeDimension 1 (Spec.map (zCH (algebraMap k ring)))) (relation:(X ⨿ X)≅pullback q q) (left_fst:coprod.inl≫relation.hom≫pullback.fst q q=𝟙 X) (left_snd:coprod.inl≫relation.hom≫pullback.snd q q=𝟙 X) (right_fst:coprod.inr≫relation.hom≫pullback.fst q q=𝟙 X) (right_snd:coprod.inr≫relation.hom≫pullback.snd q q=σ) (universal:∀ (T:zS.{u}) (a:X⟶T),σ≫a=a→ ∃! b:Base ring⟶T,q≫b=a)
attribute [instance] SignQuotient.commRing SignQuotient.algebra
abbrev coverCurve(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback (structureMap R W) Z.projection
abbrev coverToCurve(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback.fst (structureMap R W) Z.projection
abbrev coverToLevel(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback.snd (structureMap R W) Z.projection
def coverSection(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L)(s:sh Z.projection (structureMap R W)):Z.space⟶coverCurve R W Z:=
  pullback.lift s.val (𝟙 _) (by simpa using s.property)
structure EllipticFamily(S:Type u)[z0 S] where (curve:zS.{u}) (projection:curve⟶Base S) (law:GoodReductionJacobian.RelativeGroupLaw S projection) (commutative:law.IsCommutative) (proper:IsProper projection) (smooth:SmoothOfRelativeDimension 1 projection) (connected:GeometricallyConnected projection)
structure FamilyLevel(S:Type u)[z0 S](E:EllipticFamily S)(L:ℕ) where (x:sh (𝟙 (Base S)) E.projection) (y:sh (𝟙 (Base S)) E.projection) (killed_x:x.val≫E.law.schemeNsmul L=(E.law.one (𝟙 _)).val) (killed_y:y.val≫E.law.schemeNsmul L=(E.law.one (𝟙 _)).val) (avoids:∀ i j:Fin L,i.val≠0∨j.val≠0→ Disjoint (Set.range (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i.val x) (E.law.nsmul (𝟙 _) j.val y)).val) (Set.range (E.law.one (𝟙 _)).val))
def FamilyRigid(S:Type u)[z0 S](E:EllipticFamily S){L:ℕ}(M:FamilyLevel S E L):Prop:=∀ e:E.curve≅E.curve,e.hom≫E.projection=E.projection→ (E.law.one (𝟙 _)).val≫e.hom=(E.law.one (𝟙 _)).val→ M.x.val≫e.hom=M.x.val→ M.y.val≫e.hom=M.y.val→ e.hom=𝟙 E.curve
structure FamilyDescent(k R:Type u)[z1 k][z0 R][z29 k R](W:z3 R)(G:Law R W){L:ℕ}(Z:LevelScheme R W G L)(σ:SignAction R W G Z)(Q:SignQuotient k (Z.projection≫Spec.map (zCH (algebraMap k R))) σ.map) where (family:EllipticFamily Q.ring) (comparison:coverCurve R W Z⟶family.curve) (cartesian:IsPullback comparison (coverToLevel R W Z) family.projection Q.q) (origin_eq:coverSection R W Z (G.one Z.projection)≫comparison=Q.q≫(family.law.one (𝟙 _)).val) (action:coverCurve R W Z⟶coverCurve R W Z) (action_level:action≫coverToLevel R W Z=coverToLevel R W Z≫σ.map) (action_curve:action≫coverToCurve R W Z=(G.inv (coverToLevel R W Z≫Z.projection) ⟨coverToCurve R W Z,pullback.condition⟩).val) (invariant:action≫comparison=comparison)
structure LegendreAtlas(k:Type u)[z1 k](L:ℕ) where (law:Law (LegendreRing k) (legendre k)) (originLaw:IsOriginLaw (LegendreRing k) (legendre k) law) (level:LevelScheme (LegendreRing k) (legendre k) law L) (represents:Represents (LegendreRing k) (legendre k) law level) (sign:SignAction (LegendreRing k) (legendre k) law level) (quotient:SignQuotient k (level.projection≫legendreBaseMap k) sign.map) (descent:FamilyDescent k (LegendreRing k) (legendre k) law level sign quotient) (marking:FamilyLevel quotient.ring descent.family L) (rigid:FamilyRigid quotient.ring descent.family marking) (x_eq:coverSection (LegendreRing k) (legendre k) level level.level.x≫descent.comparison=quotient.q≫marking.x.val) (y_eq:coverSection (LegendreRing k) (legendre k) level level.level.y≫descent.comparison=quotient.q≫marking.y.val)
end ArithmeticThetaLegendreAtlasR0176 open ArithmeticThetaLegendreAtlasR0176 open ArithmeticThetaLegendreAtlasR0176 renaming LegendreAtlas → la
section Chart
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal rc variable {T:Type u} [z0 T] (W:zWP T)
abbrev coord(i:Fin 3):ProjModelRingCR W:=zQM (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem(i:Fin 3):coord W i∈projModelGradingCR W 1:=mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
abbrev ZChartRing:Type u:=Away (projModelGradingCR W) (coord W 2)
abbrev zChartι:Spec (zCR (ZChartRing W))⟶projModelCR W:=Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos
def xOverZ:ZChartRing W:=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ:ZChartRing W:=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
end WeierstrassCurve.DrinfeldGlobal
end Chart open WeierstrassCurve.DrinfeldGlobal namespace ArithmeticThetaLegendreComparisonR0177 rc
abbrev ChartRing(R:Type u)[z0 R](W:z3 R):=z3.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion(R:Type u)[z0 R](W:z3 R):Spec (zCR (ChartRing R W))⟶Curve R W:=z3.DrinfeldGlobal.zChartι W.toProjective
def chartScalar(R:Type u)[z0 R](W:z3 R):R→+*ChartRing R W:=(Spec.preimage (chartInclusion R W≫structureMap R W)).hom
def HasCoordinates(R:Type u)[z0 R](W:z3 R)(P:Base R⟶Curve R W)(x y:R):Prop:=P≫structureMap R W=𝟙 (Base R)∧∃ χ:ChartRing R W→+*R,P=Spec.map (zCH χ)≫chartInclusion R W∧χ (z3.DrinfeldGlobal.xOverZ W.toProjective)=x∧χ (z3.DrinfeldGlobal.yOverZ W.toProjective)=y
def completedCubic(R:Type u)[z0 R][z29 ℚ R](W:z3 R):Polynomial R:=Polynomial.X^3+Polynomial.C (W.a₂+algebraMap ℚ R (1/4)*W.a₁^2)*Polynomial.X^2+Polynomial.C (W.a₄+algebraMap ℚ R (1/2)*W.a₁*W.a₃)*Polynomial.X+Polynomial.C (W.a₆+algebraMap ℚ R (1/4)*W.a₃^2)
def SplitCubic(R:Type u)[z0 R][z29 ℚ R](W:z3 R)(e:Fin 3→ R):Prop:=(∀ i j,i≠j→ z25 (e i - e j))∧completedCubic R W=∏ i:Fin 3,(Polynomial.X - Polynomial.C (e i))
end ArithmeticThetaLegendreComparisonR0177 open ArithmeticThetaLegendreComparisonR0177 namespace ArithmeticThetaCompatibleLevelR0178 rc variable (k:Type u) [z1 k] [z2 k] (L:ℕ) (A:la k L)
abbrev TwoMarking:=FullLevel (LegendreRing k) (legendre k) A.law 2 (𝟙 (Base (LegendreRing k)))
def CanonicalTwo(B:TwoMarking k L A):Prop:=HasCoordinates (LegendreRing k) (legendre k) B.x.val 0 0∧HasCoordinates (LegendreRing k) (legendre k) B.y.val 1 0
def CompatibleAt(B:TwoMarking k L A){T:zS.{u}}(a:T⟶A.level.space):Prop:=a≫(A.law.nsmul A.level.projection (L/2) A.level.level.x).val=(a≫A.level.projection)≫B.x.val∧a≫(A.law.nsmul A.level.projection (L/2) A.level.level.y).val=(a≫A.level.projection)≫B.y.val
structure CompatibleCover(B:TwoMarking k L A) where (space:zS.{u}) (inclusion:space⟶A.level.space) (openImmersion:IsOpenImmersion inclusion) (closedImmersion:IsClosedImmersion inclusion) (compatible:CompatibleAt k L A B inclusion) (represents:∀ (T:zS.{u}) (a:T⟶A.level.space),CompatibleAt k L A B a↔∃! b:T⟶space,b≫inclusion=a) (finite:IsFinite q38) (etale:Etale q38) (surjective:Surjective q38) (degree:∀ z,(q38).finrank z=levelDegree L/6)
structure CompatibleQuotient(B:TwoMarking k L A)(C:CompatibleCover k L A B) where (sign:C.space⟶C.space) (sign_eq:sign≫C.inclusion=C.inclusion≫A.sign.map) (sign_square:sign≫sign=𝟙 _) (sign_free:IsEmpty (equalizer sign (𝟙 C.space):zS.{u})) (quotient:SignQuotient k (C.inclusion≫A.level.projection≫legendreBaseMap k) sign) (inclusion:Base quotient.ring⟶Base A.quotient.ring) (cartesian:IsPullback C.inclusion quotient.q A.quotient.q inclusion) (openImmersion:IsOpenImmersion inclusion) (closedImmersion:IsClosedImmersion inclusion) (over_eq:inclusion≫Spec.map (zCH (algebraMap k A.quotient.ring))=Spec.map (zCH (algebraMap k quotient.ring)))
end ArithmeticThetaCompatibleLevelR0178 open ArithmeticThetaCompatibleLevelR0178 open ArithmeticThetaCompatibleLevelR0178 renaming CompatibleCover → cc, CompatibleQuotient → cq, TwoMarking → tm namespace ArithmeticThetaProjectiveEffectivityR0135 rc
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace(S:Type u)[z0 S](N:ℕ):zS.{u}:=AlgebraicGeometry.Proj q39
def projectiveStructure(S:Type u)[z0 S](N:ℕ):projectiveSpace S N⟶Spec (zCR S):=Proj.toSpecZero q39≫Spec.map (zCH (algebraMap S (q39 0)))
end ArithmeticThetaProjectiveEffectivityR0135 namespace ArithmeticThetaLevelCompactificationR0179 rc
structure LevelData(k:Type u)[z1 k](L:ℕ) where (atlas:la k L) (two:tm k L atlas) (canonical:CanonicalTwo k L atlas two) (cover:cc k L atlas two) (quotient:cq k L atlas two cover)
variable (k:Type u) [z1 k] (L:ℕ)
abbrev OpenBase(D:LevelData k L):=Base D.quotient.quotient.ring
def openStructure(D:LevelData k L):OpenBase k L D⟶Base k:=Spec.map (zCH (algebraMap k D.quotient.quotient.ring))
def IsParameter(D:LevelData k L)(p:OpenBase k L D⟶Base (LegendreRing k)):Prop:=D.quotient.quotient.q≫p=D.cover.inclusion≫D.atlas.level.projection∧p≫legendreBaseMap k=openStructure k L D
structure Compactification(D:LevelData k L) where (space:zS.{u}) (projection:space⟶Base k) (inclusion:OpenBase k L D⟶space) (over_eq:inclusion≫projection=openStructure k L D) (openImmersion:IsOpenImmersion inclusion) (dense:DenseRange inclusion.base) (proper:IsProper projection) (smooth:SmoothOfRelativeDimension 1 projection) (dimension:ℕ) (embedding:space⟶ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)) (closedImmersion:IsClosedImmersion embedding) (embedding_over:embedding≫ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1)=projection)
def boundary(D:LevelData k L)(X:q1):Set X.space:=(Set.range X.inclusion.base)ᶜ
end ArithmeticThetaLevelCompactificationR0179 open ArithmeticThetaLevelCompactificationR0179 open ArithmeticThetaLevelCompactificationR0179 renaming LevelData → ld, Compactification → cp namespace WeierstrassProjModel.RelativeGroupLaw rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
abbrev idPoint:sh f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul(G:RelativeGroupLaw R f)(n:ℕ):A⟶A:=(G.nsmul f n idPoint).1
end WeierstrassProjModel.RelativeGroupLaw
section rc
structure AlgebraicGeometry.Scheme.Modules.IsInvertible{X:Scheme.{u}}(M:X.Modules):Prop where (exists_trivialization:∀ x:X,∃ (U:X.Opens),x∈U∧z30 ((zPB U.ι).obj M≅z9.unit U.toScheme.ringCatSheaf))
end
namespace AlgebraicGeometry.Scheme.Hom rc variable {A:Type u} [z0 A] {X:zS.{u}} (f:X⟶Spec (zCR A))
def constToPresheaf:(Functor.const (X.Opens)ᵒᵖ).obj (zCR A)⟶X.presheaf where
  app U:=(q59).inv≫f.appLE ⊤ U.unop le_top
  naturality U V i:=by
    simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.id_comp,Category.assoc]
    rw [zS.Hom.appLE_map]
@[reducible] def sectionsAlgebra(U:X.Opens):z29 A Γ(X,U):=(f.constToPresheaf.app (op U)).hom.toAlgebra
def kaehlerPresheaf:X.PresheafOfModules:=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf
def kaehler:X.Modules:=(zSF q7).obj f.kaehlerPresheaf
def kaehlerToSections(U:X.Opens):(f.kaehlerPresheaf.obj (op U):Type u)→ (Γ(f.kaehler,U):Type u):=fun s=> (((zSA q7).unit.app f.kaehlerPresheaf).app (op U)).hom s
end AlgebraicGeometry.Scheme.Hom
section rc variable {X Y:zS.{u}} (φ:X⟶Y) {L:Y.Modules} {U:Y.Opens}
def AlgebraicGeometry.Scheme.Modules.pullbackLocalSection(s:Γ(L,U)):Γ((Modules.pullback φ).obj L,φ ⁻¹ᵁ U):=((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s end
namespace ArithmeticThetaSheafTensor rc variable (X:zS.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor:z7 X.PresheafOfModules:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def tensorPresheaf(H K:X.Modules):X.PresheafOfModules:=H.val ⊗ K.val
def sheafTensor(H K:X.Modules):X.Modules:=(zSF q7).obj (tensorPresheaf X H K)
def tensorUnitMap(H K:X.Modules):tensorPresheaf X H K⟶(sheafTensor X H K).val:=(zSA q7).unit.app _
def tensorSection(H K:X.Modules)(U:X.Opens)(s:Γ(H,U))(t:Γ(K,U)):Γ(sheafTensor X H K,U):=(tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X,U)] t)
end ArithmeticThetaSheafTensor open ArithmeticThetaSheafTensor
section rc
def ArithmeticThetaTensorPower.tensorPower(X:zS.{u})(H:X.Modules):ℕ→ X.Modules | 0=> q24 | n+1=> sheafTensor X (tensorPower X H n) H
end
open ArithmeticThetaTensorPower open ArithmeticThetaTensorPower renaming tensorPower → tp namespace ArithmeticThetaRelativeDiscriminantR0171 rc
abbrev Hodge(R:Type u)[z0 R](W:z3 R):=(zPB (origin R W)).obj (structureMap R W).kaehler
abbrev HodgePower(R:Type u)[z0 R](W:z3 R)(n:ℕ):=tp (Base R) (Hodge R W) n
def res{X:Scheme.{u}}(F:X.Modules){U V:X.Opens}(h:V≤U)(s:Γ(F,U)):Γ(F,V):=F.presheaf.map (homOfLE h).op s
def IsFrame{X:Scheme.{u}}(F:X.Modules)(U:X.Opens)(s:Γ(F,U)):Prop:=∀ (V:X.Opens) (h:V≤U),Function.Bijective (fun a:X.presheaf.obj (Opposite.op V)=> a•res F h s)
def baseMap(R:Type u)[z0 R](S:Type u)[z0 S](ι:R→+*S):Base S⟶Base R:=Spec.map (zCH ι)
end ArithmeticThetaRelativeDiscriminantR0171 namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull rc
theorem T0.unitD._proof_1.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.Presheaf.IsLocallyInjective.{u_1,u_1,u_1,u_1+1,u_1,u_1} T9(X) T6(X) RingCat.{u_1} RingCat.instCategory.{u_1} (fun (R S:RingCat.{u_1})=> q46) RingCat.carrier.{u_1} (fun (X Y:RingCat.{u_1})=> q36) RingCat.instConcreteCategoryRingHomCarrier.{u_1} T19(X) T3(X) T3(X) T25(X):=by sorry
theorem T0.unitD._proof_2.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.Presheaf.IsLocallySurjective.{u_1,u_1,u_1,u_1+1,u_1,u_1} T9(X) T6(X) T19(X) RingCat.{u_1} RingCat.instCategory.{u_1} (fun (R S:RingCat.{u_1})=> q46) RingCat.carrier.{u_1} (fun (X Y:RingCat.{u_1})=> q36) RingCat.instConcreteCategoryRingHomCarrier.{u_1} T3(X) T3(X) T25(X):=by sorry
theorem T0.unitD._proof_3.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.{u_1,u_1,u_1,u_1+1,u_1,u_1} T9(X) T6(X) T19(X) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory.{u_1} (fun (x1 x2:AddCommGrpCat.{u_1})=> @z13.{u_1,u_1} q17 q16 (@AddZeroClass.toAddZero.{u_1} q17 (@AddMonoid.toAddZeroClass.{u_1} q17 (@SubNegMonoid.toAddMonoid.{u_1} q17 (@AddGroup.toSubNegMonoid.{u_1} q17 (@AddCommGroup.toAddGroup.{u_1} q17 (AddCommGrpCat.str.{u_1} x1)))))) (@AddZeroClass.toAddZero.{u_1} q16 (@AddMonoid.toAddZeroClass.{u_1} q16 (@SubNegMonoid.toAddMonoid.{u_1} q16 (@AddGroup.toSubNegMonoid.{u_1} q16 (@AddCommGroup.toAddGroup.{u_1} q16 (AddCommGrpCat.str.{u_1} x2))))))) AddCommGrpCat.carrier.{u_1} (fun (X Y:AddCommGrpCat.{u_1})=> @z13.instFunLike.{u_1,u_1} q19 q18 (@AddZeroClass.toAddZero.{u_1} q19 (@AddMonoid.toAddZeroClass.{u_1} q19 (@SubNegMonoid.toAddMonoid.{u_1} q19 (@AddGroup.toSubNegMonoid.{u_1} q19 (@AddCommGroup.toAddGroup.{u_1} q19 (AddCommGrpCat.str.{u_1} X)))))) (@AddZeroClass.toAddZero.{u_1} q18 (@AddMonoid.toAddZeroClass.{u_1} q18 (@SubNegMonoid.toAddMonoid.{u_1} q18 (@AddGroup.toSubNegMonoid.{u_1} q18 (@AddCommGroup.toAddGroup.{u_1} q18 (AddCommGrpCat.str.{u_1} Y))))))) AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{u_1}:=by sorry
theorem T0.unitD._proof_4.{u_1}:∀ {X:zS.{u_1}},@CategoryTheory.HasWeakSheafify T9(X) T6(X) T19(X) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory:=by sorry
run_cmd do
  for n in [``T0.unitD._proof_1,``T0.unitD._proof_2,``T0.unitD._proof_3,``T0.unitD._proof_4] do
    let some ci:=(← Lean.getEnv).find? n | throwError "missing proof cache seed"
    Lean.modifyEnv fun env=> Lean.Meta.auxLemmasExt.modifyState env fun st=> { st with lemmas:=st.lemmas.insert { type:=ci.type,isPrivate:=false,defeq:=false } (n,ci.levelParams) }
section Main
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hφ:φ≫gY=gX≫q11) (d:ℕ)
include hφ
lemma fac(U:Y.Opens):zCH (algebraMap A B)≫q42=gY.constToPresheaf.app (op U)≫φ.app U:=by
  have h1:gY.constToPresheaf.app (op U)≫φ.app U=
      (q59).inv≫(φ≫gY).appLE ⊤ (φ ⁻¹ᵁ U) le_top:=by
    change ((q59).inv≫gY.appLE ⊤ U le_top)≫φ.app U=_
    rw [Category.assoc,← zS.Hom.appLE_eq_app,zS.Hom.appLE_comp_appLE]
  have h2:zCH (algebraMap A B)≫q42=
      (q59).inv≫
        (gX≫q11).appLE ⊤ (φ ⁻¹ᵁ U) le_top:=by
    change zCH (algebraMap A B)≫
      ((zS.ΓSpecIso (zCR B)).inv≫gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top)=_
    rw [zS.Hom.comp_appLE,← Category.assoc,zS.ΓSpecIso_inv_naturality,Category.assoc]
    rfl
  rw [h1,h2,hφ]
lemma fac_apply(U:Y.Opens)(a:A):φ.app U (gY.constToPresheaf.app (op U) a)=q42 (algebraMap A B a):=by
  have:=CategoryTheory.ConcreteCategory.congr_hom (fac gY gX φ hφ U) a
  exact this.symm
def kdMap(U:Y.Opens):gY.kaehlerPresheaf.obj (op U)⟶(z12.restrictScalars (φ.app U).hom).obj (gX.kaehlerPresheaf.obj (op (φ ⁻¹ᵁ U))):=z10.KaehlerDifferential.map (fac gY gX φ hφ U)
abbrev unit1(V:X.Opens):gX.kaehlerPresheaf.obj (op V)⟶gX.kaehler.val.obj (op V):=((zSA q7).unit.app gX.kaehlerPresheaf).app (op V)
lemma unit1_apply(V:X.Opens)(x:gX.kaehlerPresheaf.obj (op V)):unit1 gX V x=gX.kaehlerToSections V x:=rfl
omit hφ in
def dK{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C))(V:Z.Opens)(b:Γ(Z,V)):(g.kaehlerPresheaf.obj (op V):Type u):=z10.KaehlerDifferential.d (f:=g.constToPresheaf.app (op V)) b
omit hφ in
lemma kp_map_dK{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C)){V V':Z.Opens}(i:op V⟶op V')(b:Γ(Z,V)):g.kaehlerPresheaf.map i (dK g V b)=dK g V' (Z.presheaf.map i b):=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d g.constToPresheaf i b
omit hφ in
lemma kp_hom_ext{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C))(V:Z.Opens){M:z12 Γ(Z,V)}{α β:g.kaehlerPresheaf.obj (op V)⟶M}(h:∀ b:Γ(Z,V),α (dK g V b)=β (dK g V b)):α=β:=z10.KaehlerDifferential.ext h
omit hφ in
lemma map_unit1{V V':X.Opens}(j:op V⟶op V')(x:gX.kaehlerPresheaf.obj (op V)):gX.kaehler.val.map j (unit1 gX V x)=unit1 gX V' (gX.kaehlerPresheaf.map j x):=(z8.naturality_apply ((zSA q7).unit.app gX.kaehlerPresheaf) j x).symm
omit hφ in
lemma φ_naturality_apply{U U':Y.Opens}(i:op U⟶op U')(b:Γ(Y,U)):X.presheaf.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op (φ.app U b)=φ.app U' (Y.presheaf.map i b):=(CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm
def k1app(U:Y.Opens):gY.kaehlerPresheaf.obj (op U)⟶((zPF φ).obj gX.kaehler).val.obj (op U):=kdMap gY gX φ hφ U≫(z12.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))
lemma k1app_dK(U:Y.Opens)(b:Γ(Y,U)):k1app gY gX φ hφ U (dK gY U b)=unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)):=by
  show unit1 gX (φ ⁻¹ᵁ U) (z10.KaehlerDifferential.map (fac gY gX φ hφ U)
    (z10.KaehlerDifferential.d b))=_
  rw [z10.KaehlerDifferential.map_d]
  rfl
def k1pre:gY.kaehlerPresheaf⟶((zPF φ).obj gX.kaehler).val where
  app U:=k1app gY gX φ hφ U.unop
  naturality {U U'} i:=by
    obtain ⟨U⟩:=U; obtain ⟨U'⟩:=U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b))=
      gX.kaehler.val.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK,k1app_dK,k1app_dK,map_unit1,kp_map_dK,φ_naturality_apply]
abbrev adjY:=zSA (𝟙 Y.ringCatSheaf.obj)
def k1:gY.kaehler⟶(zPF φ).obj gX.kaehler:=((adjY (Y:=Y)).homEquiv gY.kaehlerPresheaf ((zPF φ).obj gX.kaehler)).symm (k1pre gY gX φ hφ)
end Main
end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange rc
section DifferentialMap
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hφ:φ≫gY=gX≫q11)
def differentialMap:(zPB φ).obj gY.kaehler⟶gX.kaehler:=((zPA φ).homEquiv _ _).symm (k1 gY gX φ hφ)
theorem differentialMap_isIso(hc:CategoryTheory.IsPullback φ gX gY (q11))[SmoothOfRelativeDimension 1 gY]:IsIso (differentialMap gY gX φ hφ):=by sorry
end DifferentialMap variable {X Y:Scheme.{u}}
def pullbackEqIso{f g:X⟶Y}(h:f=g)(M:Y.Modules):(zPB f).obj M≅(zPB g).obj M:=
  eqToIso (by cases h; rfl)
def squarePullbackIso{A B X Y:Scheme.{u}}(a:A⟶B)(s:B⟶Y)(t:A⟶X)(b:X⟶Y)(h:a≫s=t≫b)(M:Y.Modules):(zPB a).obj ((zPB s).obj M)≅(zPB t).obj ((zPB b).obj M):=(zPC a s).app M≪≫pullbackEqIso h M≪≫((zPC t b).app M).symm
section PointedComparison
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hc:CategoryTheory.IsPullback φ gX gY (q11)) [SmoothOfRelativeDimension 1 gY] (s:Spec (zCR A)⟶Y) (t:Spec (zCR B)⟶X) (hpt:t≫φ=q11≫s)
def pointedDifferentialIso:(zPB (q11)).obj ((zPB s).obj gY.kaehler)≅(zPB t).obj gX.kaehler:=by
  letI:=differentialMap_isIso gY gX φ hc.w hc
  exact squarePullbackIso _ s t φ hpt.symm gY.kaehler≪≫
    (zPB t).mapIso (asIso (differentialMap gY gX φ hc.w))
end PointedComparison
end ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange namespace ArithmeticThetaOpenHodgeR0180 rc
abbrev zero{S:Type u}[z0 S](E:EllipticFamily S):Base S⟶E.curve:=(E.law.one (𝟙 _)).val
abbrev hodge{S:Type u}[z0 S](E:EllipticFamily S):=(zPB (zero E)).obj E.projection.kaehler
abbrev power{S:Type u}[z0 S](E:EllipticFamily S)(n:ℕ):=tp (Base S) (hodge E) n
structure Test(S:Type u)[z0 S](E:EllipticFamily S)(R:Type u)[z0 R](W:z3 R)(G:Law R W) where (scalar:S→+*R) (map:Curve R W⟶E.curve) (cartesian:IsPullback map (structureMap R W) E.projection (baseMap S R scalar)) (origin_eq:origin R W≫map=baseMap S R scalar≫zero E) (nsmul_eq:∀ n,G.schemeNsmul n≫map=map≫E.law.schemeNsmul n)
def comparison{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G):(zPB q52).obj (hodge E)≅Hodge R W:=by
  letI:z29 S R:=C.scalar.toAlgebra
  letI:SmoothOfRelativeDimension 1 E.projection:=E.smooth
  exact pointedDifferentialIso E.projection (structureMap R W) C.map
    C.cartesian (zero E) (origin R W) C.origin_eq
end ArithmeticThetaOpenHodgeR0180 open ArithmeticThetaOpenHodgeR0180
section rc variable (k:Type u) [z1 k] (L:ℕ) (A:la k L)
def ArithmeticThetaCompatibleLevelR0178.Classifies(B:tm k L A)(C:cc k L A B)(Q:cq k L A B C)(R:Type u)[z0 R][z29 k R](W:z3 R)(G:Law R W)(M:q58)(b:Base R⟶Base Q.quotient.ring)(f:Curve R W⟶A.descent.family.curve):Prop:=b≫Spec.map (zCH (algebraMap k Q.quotient.ring))= Spec.map (zCH (algebraMap k R))∧IsPullback f (structureMap R W) A.descent.family.projection (b≫Q.inclusion)∧origin R W≫f=(b≫Q.inclusion)≫(A.descent.family.law.one (𝟙 _)).val∧M.x.val≫f=(b≫Q.inclusion)≫A.marking.x.val∧M.y.val≫f=(b≫Q.inclusion)≫A.marking.y.val
end
namespace ArithmeticThetaTateSeries rc variable {k:Type u} [z1 k]
def monomial(a:k)(n:ℕ):z4 k:=z4.C a*z4.X ^ n
def xTerm(v:z4 k):z4 k:=v*((1-v)⁻¹)^2
def yTerm(v:z4 k):z4 k:=v*(1+v)*((1-v)⁻¹)^3
def partialX(d i:ℕ)(a:k)(N:ℕ):z4 k:=xTerm (monomial a i)+(∑ j∈Finset.range N,(xTerm (monomial a (d*(j+1)+i))+xTerm (monomial a⁻¹ (d*(j+1)-i)))) - 2*∑ j∈Finset.range N,z4.C ((j+1:ℕ):k)*monomial 1 (d*(j+1))*(1 - monomial 1 (d*(j+1)))⁻¹
def partialY(d i:ℕ)(a:k)(N:ℕ):z4 k:=z4.C (2:k)⁻¹*(yTerm (monomial a i)+∑ j∈Finset.range N,(yTerm (monomial a (d*(j+1)+i)) - yTerm (monomial a⁻¹ (d*(j+1)-i))))
def tateX(d i:ℕ)(a:k):z4 k:=z4.mk fun n=> z4.coeff n (partialX d i a (n+1))
def tateY(d i:ℕ)(a:k):z4 k:=z4.mk fun n=> z4.coeff n (partialY d i a (n+1))
def theta(k:Type u)[z1 k]:z4 k:=z4.mk fun n=> (if n=0 then 1 else 0)+2*((Finset.filter (fun j:ℕ=> j^2=n) (Finset.Icc 1 n)).card:k)
end ArithmeticThetaTateSeries
section rc variable (k:Type u) [z1 k] [z2 k]
def ArithmeticThetaCubicModelR0144.rootSeries(r:ℕ)(j:Fin 3):z4 k:=if j.val=0 then ArithmeticThetaTateSeries.tateX r 0 (-1) else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val=1 then 1 else -1) end
open ArithmeticThetaCubicModelR0144 namespace ArithmeticThetaCompactifiedDifferentialR0145 rc variable (k:Type u) [z1 k] [z2 k]
def root(r:ℕ)(j:Fin 3):z5 k:=q2 (rootSeries k r j)
def curve(r:ℕ):z3 (z5 k) where
  a₁:=0
  a₂:=-(root k r 0+root k r 1+root k r 2)
  a₃:=0
  a₄:=root k r 0*root k r 1+root k r 0*root k r 2+root k r 1*root k r 2
  a₆:=-(root k r 0*root k r 1*root k r 2)
abbrev projectiveCurve(r:ℕ):zS.{u}:=projModelCR (curve k r).toProjective
def projectiveStructure(r:ℕ):projectiveCurve k r⟶Spec (zCR (z5 k)):=projModelStrCR (curve k r).toProjective
abbrev ChartRing(r:ℕ):=z3.DrinfeldGlobal.ZChartRing (curve k r).toProjective
def chartInclusion(r:ℕ):Spec (zCR (ChartRing k r))⟶projectiveCurve k r:=z3.DrinfeldGlobal.zChartι (curve k r).toProjective
def relativeD{F:Type u}[z0 F]{C:zS.{u}}(f:C⟶Spec (zCR F))(U:C.Opens)(a:C.presheaf.obj (Opposite.op U)):Γ(f.kaehler,U):=
  letI:z29 F (C.presheaf.obj (Opposite.op U)):=f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (Opposite.op U)) a)
end ArithmeticThetaCompactifiedDifferentialR0145
section rc variable (k:Type u) [z1 k] [z2 k] (r:ℕ)
def ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart.chartScalar:z5 k→+*ChartRing k r:=(z24.fromZeroRingHom (projModelGradingCR (curve k r).toProjective) (Submonoid.powers (coord (curve k r).toProjective 2))).comp (algebraMap (z5 k) (projModelGradingCR (curve k r).toProjective 0)) end
namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential rc
section ChartEquiv
variable {B:Type u} [z0 B] {C:zS.{u}} (i:Spec (zCR B)⟶C) [IsOpenImmersion i]
def chartRingEquiv:Γ(C,i ''ᵁ ⊤) ≃+*B:=((i.appIso ⊤)≪≫zS.ΓSpecIso (zCR B)).commRingCatIsoToRingEquiv
end ChartEquiv variable (k:Type u) [Field k] [CharZero k] (r:ℕ)
local instance zchartAlgebra:z29 (z5 k) (ChartRing k r):=(ProjectiveCubicChart.chartScalar k r).toAlgebra
variable {C:zS.{u}} (E:C≅projectiveCurve k r)
abbrev zLeg:=chartInclusion k r≫E.inv
instance zLeg_open:IsOpenImmersion (zLeg k r E):=by dsimp [zLeg,chartInclusion]; infer_instance
abbrev zOpen:C.Opens:=zLeg k r E ''ᵁ ⊤
abbrev zSection:ChartRing k r ≃+*Γ(C,zOpen k r E):=(chartRingEquiv (zLeg k r E)).symm
end ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential namespace ArithmeticThetaTateCuspsR0181 rc variable (k:Type u) [z1 k] [z2 k] (L:ℕ)
abbrev TateCurve:=ArithmeticThetaCompactifiedDifferentialR0145.curve k L
abbrev Disk:=Base (z4 k)
abbrev Puncture:=Base (z5 k)
def genericInclusion:Puncture k⟶Disk k:=Spec.map (zCH (q2))
def diskStructure:Disk k⟶Base k:=Spec.map (zCH (algebraMap k (z4 k)))
def closedPoint:Disk k:=⟨IsLocalRing.maximalIdeal (z4 k),inferInstance⟩
structure TateLevel where (elliptic:(TateCurve k L).IsElliptic) (law:Law (z5 k) (TateCurve k L)) (originLaw:IsOriginLaw (z5 k) (TateCurve k L) law) (marking:FullLevel (z5 k) (TateCurve k L) law L (𝟙 (Puncture k)))
def Extends(D:ld k L)(X:q1)(b:Puncture k⟶OpenBase k L D)(d:Disk k⟶X.space):Prop:=d≫X.projection=diskStructure k∧genericInclusion k≫d=b≫X.inclusion∧d (closedPoint k)∈boundary k L D X
end ArithmeticThetaTateCuspsR0181 open ArithmeticThetaTateCuspsR0181 namespace ArithmeticThetaBoundaryHodgeR0182 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ)
abbrev CurveFrame:=(z9.unit (q9).ringCatSheaf:(q9).Modules)≅(structureMap (z5 k) (TateCurve k L)).kaehler
def Normalized(δ:CurveFrame k L):Prop:=
  let E:=Iso.refl (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k L)
  let U:=ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen k L E
  let x:=ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (z3.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)
  let y:=ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (z3.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)
  ArithmeticThetaCompactifiedDifferentialR0145.relativeD
    (structureMap (z5 k) (TateCurve k L)) U x=
      (2*y)•zS.Modules.Hom.app δ.hom U (1:Γ(q9,U))
def hodgeGenerator(δ:CurveFrame k L):Γ(q33,⊤):=
  res _ (by simp) (zS.Modules.pullbackLocalSection
    (origin (z5 k) (TateCurve k L)) (zS.Modules.Hom.app δ.hom ⊤ (1:Γ(q9,⊤))))
structure Test(D:ld k L) where (level:TateLevel k L) (base:Puncture k⟶OpenBase k L D) (map:q9⟶D.atlas.descent.family.curve) (classifies:ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two D.cover D.quotient (z5 k) (TateCurve k L) level.law level.marking base map) (nsmul_eq:∀ n,level.law.schemeNsmul n≫map=map≫D.atlas.descent.family.law.schemeNsmul n) (differential:CurveFrame k L) (normalized:Normalized k L differential)
structure DiskTest(D:ld k L)(X:q1) extends Test k L D where (disk:Disk k⟶X.space) (extends_eq:Extends k L D X base disk)
abbrev openHodge(D:ld k L):=(zPB D.quotient.inclusion).obj q47
abbrev openPower(D:ld k L)(n:ℕ):=tp (OpenBase k L D) (openHodge k L D) n
def testIso{D:ld k L}(T:Test k L D):(zPB (T.base≫D.quotient.inclusion)).obj q47≅q33:=by
  let ι:D.atlas.quotient.ring→+*z5 k:=
    (Spec.preimage (T.base≫D.quotient.inclusion)).hom
  have hmap:baseMap D.atlas.quotient.ring (z5 k) ι=
      T.base≫D.quotient.inclusion:=Spec.map_preimage _
  let C:ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring
      D.atlas.descent.family (z5 k) (TateCurve k L) T.level.law:=
    { scalar:=ι
      map:=T.map
      cartesian:=by rw [hmap]; exact T.classifies.2.1
      origin_eq:=by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq:=T.nsmul_eq }
  exact pullbackEqIso hmap.symm q47≪≫comparison C
def openTestIso{D:ld k L}(T:Test k L D):(zPB T.base).obj (openHodge k L D)≅q33:=(zPC T.base D.quotient.inclusion).app _≪≫testIso k L T
structure Extension(D:ld k L)(X:q1) where (line:X.space.Modules) (invertible:zS.Modules.IsInvertible line) (onOpen:(zPB X.inclusion).obj line≅openHodge k L D)
def diskGenericIso{D:ld k L}{X:q1}(H:Extension k L D X)(T:DiskTest k L D X):(zPB (genericInclusion k)).obj (q50)≅q33:=(zPC (genericInclusion k) T.disk).app H.line≪≫pullbackEqIso T.extends_eq.2.1 H.line≪≫ ((zPC T.base X.inclusion).app H.line).symm≪≫(zPB T.base).mapIso H.onOpen≪≫openTestIso k L T.toTest
def ExtendsGenerator{D:ld k L}{X:q1}(H:Extension k L D X)(T:DiskTest k L D X)(η:Γ(q50,⊤)):Prop:=
  IsFrame (q50) ⊤ η∧
  res _ (by simp) ((diskGenericIso k L H T).hom.app _
    (zS.Modules.pullbackLocalSection (genericInclusion k) η))=
      hodgeGenerator k L T.differential
def Canonical{D:ld k L}{X:q1}(H:Extension k L D X):Prop:=∀ T:DiskTest k L D X,∃! η:Γ(q50,⊤),ExtendsGenerator k L H T η
end ArithmeticThetaBoundaryHodgeR0182 open ArithmeticThetaBoundaryHodgeR0182 open ArithmeticThetaBoundaryHodgeR0182 renaming Extension → ex, Canonical → ca namespace ArithmeticThetaSheafTensor rc variable (X:zS.{u})
end ArithmeticThetaSheafTensor
section rc
def ArithmeticThetaTensorPower.tensorPowerSection(X:zS.{u})(H:X.Modules):(n:ℕ)→ (U:X.Opens)→ Γ(H,U)→ Γ(tp X H n,U) | 0,U,_=> (1:Γ(X,U)) | n+1,U,s=> tensorSection X (tp X H n) H U (tensorPowerSection X H n U s) s
end
namespace P458 rc
def pullSection{X Y:Scheme.{u}}(f:X⟶Y){H:Y.Modules}{U:Y.Opens}(s:Γ(H,U)):Γ((zPB f).obj H,f ⁻¹ᵁ U):=((zPA f).unit.app H).app U s
def Compatible{X Y:Scheme.{u}}(f:X⟶Y)(H K:Y.Modules)(M N:X.Modules)(e:(zPB f).obj H≅M)(d:(zPB f).obj K≅N)(q:(zPB f).obj (sheafTensor Y H K)≅sheafTensor X M N):Prop:= ∀ (U:Y.Opens) (s:Γ(H,U)) (t:Γ(K,U)),q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t))=tensorSection X M N (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor{X Y:Scheme.{u}}(f:X⟶Y)(H K:Y.Modules)(M N:X.Modules)(e:(zPB f).obj H≅M)(d:(zPB f).obj K≅N):∃! q:(zPB f).obj (sheafTensor Y H K)≅sheafTensor X M N,Compatible f H K M N e d q:=by sorry
end P458
section rc
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
def ArithmeticThetaPullback.pullback_unit_iso(X Y:zS.{u})(p:X⟶Y):(zPB p).obj (z9.unit Y.ringCatSheaf)≅q24:=by
  letI:(TopologicalSpace.Opens.map p.base).Final:=by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤,by simp⟩
  let e:=asIso (z9.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
end
open ArithmeticThetaPullback
section rc
def P505.binary{X Y:Scheme.{u}}(f:X⟶Y)(H K:Y.Modules):(zPB f).obj (sheafTensor Y H K)≅sheafTensor X ((zPB f).obj H) ((zPB f).obj K):=Classical.choose (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists end
namespace ArithmeticThetaPullback rc
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor(X:zS.{u}):z7 X.PresheafOfModules:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def sheafTensorMap(X:zS.{u}){H H' K K':X.Modules}(f:H⟶H')(g:K⟶K'):sheafTensor X H K⟶sheafTensor X H' K':=(zSF q7).map (f.val ⊗ₘ g.val)
def sheafTensorCongr(X:zS.{u}){H H' K K':X.Modules}(e:H≅H')(d:K≅K'):sheafTensor X H K≅sheafTensor X H' K':=(zSF q7).mapIso (tensorIso ((z9.forget _).mapIso e) ((z9.forget _).mapIso d))
end ArithmeticThetaPullback
section rc
def P505.powerComparison(X Y:zS.{u})(f:X⟶Y)(H:Y.Modules):(n:ℕ)→ (zPB f).obj (tp Y H n)≅tp X ((zPB f).obj H) n | 0=> pullback_unit_iso X Y f | n+1=> binary f (tp Y H n) H≪≫sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end
namespace ArithmeticThetaGeometricNormR0150 rc variable {X Y:zS.{u}} [IsIntegral X] [IsIntegral Y]
def IsFieldMap(f:X⟶Y)(φ:Y.functionField→+*X.functionField):Prop:=X.fromSpecStalk (genericPoint X)≫f=Spec.map (zCH φ)≫Y.fromSpecStalk (genericPoint Y)
def fieldNorm(φ:Y.functionField→+*X.functionField)(g:X.functionField):Y.functionField:=
  letI:=φ.toAlgebra
  z29.norm Y.functionField g
end ArithmeticThetaGeometricNormR0150 namespace ArithmeticThetaGeneralEllipticKatoR0168 rc variable (F:Type u) [z1 F]
abbrev Curve(W:z3 F):zS.{u}:=projModelCR W.toProjective
def structureMap(W:z3 F):Curve F W⟶Spec (zCR F):=projModelStrCR W.toProjective
def origin(W:z3 F):Spec (zCR F)⟶Curve F W:=(kwZeroSect F W).val
abbrev Law(W:z3 F):=WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)
def IsOriginLaw(W:z3 F)(G:Law F W):Prop:=(∀ {V:zS.{u}} (t:V⟶Spec (zCR F)),(G.one t).val=t≫origin F W)∧(∀ {V:zS.{u}} (t:V⟶Spec (zCR F)) (x y:sh t (structureMap F W)),G.mul t x y=G.mul t y x)
section
attribute [local instance 2000] HenselianLocalRing.toIsLocalRing
def originPoint(W:z3 F):Curve F W:=origin F W (IsLocalRing.closedPoint F)
end
def katoOrder(W:z3 F)(G:Law F W)(c:ℕ)(x:Curve F W):ℤ:=by
  classical
  exact (if x=originPoint F W then (c:ℤ)^2 else 0) - (if G.schemeNsmul c x=originPoint F W then 1 else 0)
def HasKatoDivisor(W:z3 F)(G:Law F W)(c:ℕ)[IsIntegral (Curve F W)][IsLocallyNoetherian (Curve F W)](g:(Curve F W).functionField):Prop:=g≠0∧∀ x:Curve F W,zS.ord g x=katoOrder F W G c x
def IsKatoFunction(W:z3 F)(G:Law F W)(c:ℕ)[IsIntegral (Curve F W)][IsLocallyNoetherian (Curve F W)](g:(Curve F W).functionField):Prop:=HasKatoDivisor F W G c g∧∀ d:ℕ,0 < d→ Nat.Coprime c d→ ∀ φ:(Curve F W).functionField→+*(Curve F W).functionField,q63→ ArithmeticThetaGeometricNormR0150.fieldNorm φ g=g
end ArithmeticThetaGeneralEllipticKatoR0168 namespace ArithmeticThetaRelativeKatoR0169 rc variable (R:Type u) [z0 R] [z15 R]
abbrev GenericCurve(W:z3 R):zS.{u}:=ArithmeticThetaGeneralEllipticKatoR0168.Curve (z22 R) (W.map q8)
structure GenericComparison(W:z3 R)(G:Law R W)[q37][q49] where (law:ArithmeticThetaGeneralEllipticKatoR0168.Law (z22 R) (W.map q8)) (originLaw:ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (z22 R) (W.map q8) law) (map:GenericCurve R W⟶Curve R W) (cartesian:IsPullback map (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (z22 R) (W.map q8)) (structureMap R W) (Spec.map (zCH q8))) (origin_eq:ArithmeticThetaGeneralEllipticKatoR0168.origin (z22 R) (W.map q8)≫map=Spec.map (zCH q8)≫origin R W) (multiplication_eq:∀ n:ℕ,law.schemeNsmul n≫map=map≫G.schemeNsmul n) (field:(Curve R W).functionField ≃+*(GenericCurve R W).functionField) (field_eq:ArithmeticThetaGeometricNormR0150.IsFieldMap map field.toRingHom)
def katoOrder(W:z3 R)(G:Law R W)(c:ℕ)(x:Curve R W):ℤ:=by
  classical
  exact (if x∈Set.range (origin R W) then (c:ℤ)^2 else 0) - (if G.schemeNsmul c x∈Set.range (origin R W) then 1 else 0)
variable (W:z3 R) (G:Law R W) variable [q37] [q40]
def IsRelativeKato(c:ℕ)(g:(Curve R W).functionField):Prop:=g≠0∧(∀ x:Curve R W,Order.coheight x=1→ zS.ord g x=katoOrder R W G c x)∧(∀ d:ℕ,0 < d→ Nat.Coprime c d→ ∀ φ:(Curve R W).functionField→+*(Curve R W).functionField,q63→ ArithmeticThetaGeometricNormR0150.fieldNorm φ g=g)
end ArithmeticThetaRelativeKatoR0169 namespace ArithmeticThetaRelativeKatoNaturalityR0170 rc variable (R:Type u) [z0 R] [z15 R] variable (W:z3 R) (G:Law R W)
def identityIdeal:(Curve R W).IdealSheafData:=(origin R W).ker
def torsionIdeal(n:ℕ):(Curve R W).IdealSheafData:=(identityIdeal R W).comap (G.schemeNsmul n)
variable [q37] [q40] variable [q49] [q55]
def Normalized(c:ℕ)(g:(Curve R W).functionField):Prop:=IsRelativeKato R W G c g∧∀ C:GenericComparison R W G,ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (z22 R) (W.map q8) C.law c (C.field g)
def HasValue(P:Spec (zCR R)⟶Curve R W)(g:(Curve R W).functionField)(v:R):Prop:=∃ (U:(Curve R W).Opens) (hU:z30 U) (e:(⊤:(Spec (zCR R)).Opens)≤P ⁻¹ᵁ U) (a:q51),z25 a∧@zS.germToFunctionField (Curve R W) _ U hU a=g∧(zS.ΓSpecIso (zCR R)).hom (P.appLE U ⊤ e a)=v
end ArithmeticThetaRelativeKatoNaturalityR0170 open ArithmeticThetaRelativeKatoNaturalityR0170 namespace ArithmeticThetaRelativeDiscriminantR0171 rc
def localDifferential(R:Type u)[z0 R](W:z3 R)(U:(Curve R W).Opens)(a:q51):Γ(Hodge R W,(origin R W) ⁻¹ᵁ U):=zS.Modules.pullbackLocalSection (origin R W) (ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U a)
def localPower(R:Type u)[z0 R](W:z3 R)(n:ℕ)(U:(Curve R W).Opens)(a:q51):Γ(HodgePower R W n,(origin R W) ⁻¹ᵁ U):=tensorPowerSection (Base R) (Hodge R W) n ((origin R W) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R:Type u) [z0 R] [z15 R] variable (W:z3 R) (G:Law R W)
def IdentityChart(c:ℕ)(U:(Curve R W).affineOpens)(a:q48):Prop:=IsRegular a∧(identityIdeal R W).ideal U=Ideal.span ({a}:Set _)∧(torsionIdeal R W G c).ideal U=(identityIdeal R W).ideal U
variable [q37]
def RepresentsInitial(c:ℕ)(g:(Curve R W).functionField)(d:Γ(HodgePower R W (c^2-1),⊤)):Prop:=∀ (U:(Curve R W).affineOpens) [z30 U.1] (a:q48),IdentityChart R W G c U a→ ∃ ε:(q48)ˣ,(c:(Curve R W).functionField)*g=(Curve R W).germToFunctionField U.1 ((ε:_)*a^(c^2-1))∧ res (HodgePower R W (c^2-1)) le_top d=(origin R W).app U.1 (ε:_)•localPower R W (c^2-1) U.1 a
end ArithmeticThetaRelativeDiscriminantR0171
section rc
def ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.powerCongr(X:zS.{u}){H K:X.Modules}(e:H≅K):(n:ℕ)→ tp X H n≅tp X K n | 0=> Iso.refl _ | n+1=> sheafTensorCongr X (powerCongr X e n) e
end
section rc
def ArithmeticThetaPullback.pullbackGlobalSection{X Y:Scheme.{u}}(p:X⟶Y)(M:Y.Modules):Γ(M,⊤)→ Γ((zPB p).obj M,p ⁻¹ᵁ (⊤:Y.Opens)):=fun s=> ((zPA p).unit.app M).app ⊤ s end
section rc
def P509.HodgeBaseChange.tensorComparison{X Y:Scheme.{u}}(p:X⟶Y)(H:Y.Modules)(K:X.Modules)(e:(zPB p).obj H≅K)(n:ℕ):(zPB p).obj (tp Y H n)≅tp X K n:=P505.powerComparison X Y p H n≪≫powerCongr X e n end
namespace P509.OpenHodge rc
def powerComparison{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G)(n:ℕ):(zPB q52).obj (power E n)≅HodgePower R W n:=P509.HodgeBaseChange.tensorComparison q52 (hodge E) (Hodge R W) (comparison C) n
def pullSection{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G)(n:ℕ)(s:Γ(power E n,⊤)):Γ(HodgePower R W n,⊤):=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (zS.Modules.pullbackLocalSection q52 s))
def IsD2{S:Type u}[z0 S](E:EllipticFamily S)(d:Γ(power E 24,⊤)):Prop:=IsFrame (power E 24) ⊤ d∧∀ (R:Type u) [z0 R] [z15 R] [z17 R] [z16 R] [z29 ℚ R] (W:z3 R) [W.IsElliptic] [q37] [q40] [q49] [q55] (G:Law R W),IsOriginLaw R W G→ ∀ (C:Test S E R W G) (g:(Curve R W).functionField),Normalized R W G 5 g→ RepresentsInitial R W G 5 g (pullSection C 24 d)
end P509.OpenHodge namespace P509.BoundaryHodge rc variable (k:Type) [z1 k] [z2 k] (L:ℕ)
def pullToOpen{D:ld k L}(n:ℕ)(s:Γ(power D.atlas.descent.family n,⊤)):Γ(openPower k L D n,⊤):=
  res _ (by simp) ((P505.powerComparison _ _
    D.quotient.inclusion q47 n).hom.app _
      (zS.Modules.pullbackLocalSection D.quotient.inclusion s))
def restrictPower{D:ld k L}{X:q1}(H:ex k L D X)(n:ℕ)(s:Γ(tp X.space H.line n,⊤)):Γ(openPower k L D n,⊤):=
  res _ (by simp) ((P509.HodgeBaseChange.tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (zS.Modules.pullbackLocalSection X.inclusion s))
end P509.BoundaryHodge
section rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1)
theorem P485.componentIsOpen(x:X.space):IsOpen (irreducibleComponent x):=by sorry end
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1)
theorem compactComponent._proof_1:∀ (k : Type) [inst : Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)   (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : ↥X.space), IsOpen (irreducibleComponent x):=by sorry
run_cmd do
  let n := `ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent._proof_1
  let some ci := (← Lean.getEnv).find? n | throwError "missing proof cache seed"
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert { type := ci.type, isPrivate := false, defeq := false } (n, ci.levelParams) }
def compactComponent(x:X.space):X.space.Opens:=⟨irreducibleComponent x,compactComponent._proof_1 k L D X x⟩
end ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182 namespace ArithmeticThetaComponentDegreeR0184 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1) (x:X.space)
abbrev componentOpen:X.space.Opens:=CompactHodgeLatticeExtensionR0182.compactComponent k L D X x
abbrev Component:zS:=(componentOpen k L D X x).toScheme
abbrev inclusion:Component k L D X x⟶X.space:=(componentOpen k L D X x).ι
abbrev projection:Component k L D X x⟶Spec (zCR k):=inclusion k L D X x≫X.projection
theorem componentIntegral:IsIntegral q5:=by sorry
attribute [instance] componentIntegral
theorem componentLocallyNoetherian:IsLocallyNoetherian q5:=by sorry
attribute [instance] componentLocallyNoetherian
def cuspSet:Set q5:={y | inclusion k L D X x y∈boundary k L D X}
abbrev Cusps:={y:Component k L D X x//y∈cuspSet k L D X x}
abbrev hodge(H:ex k L D X):(q5).Modules:=(zPB (inclusion k L D X x)).obj H.line
abbrev power(H:ex k L D X)(n:ℕ):(Component k L D X x).Modules:=tp (Component k L D X x) (hodge k L D X x H) n
end ArithmeticThetaComponentDegreeR0184 open ArithmeticThetaComponentDegreeR0184 namespace ArithmeticThetaLineRoot rc
structure LocalFrame(X:zS.{u})(H:X.Modules)(U:X.Opens) where (equiv (V:X.Opens) (hVU:V≤U):Γ(X,V) ≃ₗ[Γ(X,V)] Γ(H,V)) (naturality (V W:X.Opens) (hWV:W≤V) (hVU:V≤U) (a:Γ(X,V)):H.presheaf.map (homOfLE hWV).op (equiv V hVU a)=equiv W (hWV.trans hVU) (X.presheaf.map (homOfLE hWV).op a))
variable (X:zS.{u}) [IsIntegral X]
structure NormalFrameCover(H:X.Modules)(ι:Type v) where (opens:ι→ X.Opens) (covers:(⊤:X.Opens)≤ iSup opens) (nonempty:∀ i,z30 (opens i)) (affine:∀ i,IsAffineOpen (opens i)) (normal:∀ i,z16 Γ(X,opens i)) (frame:∀ i,LocalFrame X H (opens i))
instance {X:zS.{u}} {H:X.Modules} {ι:Type v} (C:NormalFrameCover X H ι) (i:ι):z30 (C.opens i):=C.nonempty i
end ArithmeticThetaLineRoot open ArithmeticThetaLineRoot open ArithmeticThetaLineRoot renaming LocalFrame → lf, NormalFrameCover → nf namespace ArithmeticThetaNormalizedSections rc
def sectionCoordinate(X:zS.{u})(H:X.Modules)(U:X.Opens)(e:lf X H U)(s:Γ(H,⊤)):Γ(X,U):=(e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)
def sectionCoefficient(X:zS.{u})[IsIntegral X](H:X.Modules)(U:X.Opens)[z30 U](e:lf X H U)(s:Γ(H,⊤)):X.functionField:=X.germToFunctionField U (sectionCoordinate X H U e s)
end ArithmeticThetaNormalizedSections open ArithmeticThetaNormalizedSections namespace ArithmeticThetaSectionOrder rc
def localOrder(X:zS.{u})[IsIntegral X][q13](H:X.Modules){ι:Type v}(C:nf X H ι)(s:Γ(H,⊤))(i:ι)(x:X):ℤ:=zS.ord (sectionCoefficient X H (C.opens i) (C.frame i) s) x
def MatchesSectionOrder(X:zS.{u})[IsIntegral X][q13](H:X.Modules){ι:Type v}(C:nf X H ι)(s:Γ(H,⊤))(D:X→₀ ℤ):Prop:=∀ (i:ι) (x:X),x∈C.opens i→ D x=localOrder X H C s i x
end ArithmeticThetaSectionOrder open ArithmeticThetaSectionOrder
section rc
def ArithmeticThetaNormalizedSections.NormalAffine(X:zS.{u}):Prop:=∀ U:X.Opens,IsAffineOpen U→ ∀ [z30 U],z16 Γ(X,U) end
namespace P509.NormalizedSections
rc
open ArithmeticThetaTensorPower
def pullbackPowerSection {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : Γ(tensorPower Y ((Scheme.Modules.pullback p).obj H) n, ⊤) := (P505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤ : X.Opens)) (ArithmeticThetaPullback.pullbackGlobalSection p (tensorPower X H n) F)
end P509.NormalizedSections
namespace P509.ComponentDegree
rc
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)
def restrict (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(power k L D X x H n, ⊤) := P509.NormalizedSections.pullbackPowerSection (inclusion k L D X x) H.line n s
def IsCompactD2 (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop := ∃ d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤), P509.OpenHodge.IsD2 D.atlas.descent.family d ∧ P509.BoundaryHodge.restrictPower k L H 24 s = P509.BoundaryHodge.pullToOpen k L 24 d
end P509.ComponentDegree
namespace ArithmeticThetaPalomarSplit515
rc
theorem splitComponentDiscriminantDivisor : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), P509.ComponentDegree.IsCompactD2 k L D X H s → (P509.ComponentDegree.restrict k L D X x H 24 s) ≠ 0 ∧ ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) ι), ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) C (P509.ComponentDegree.restrict k L D X x H 24 s) E ∧ ∀ y : ArithmeticThetaComponentDegreeR0184.Component k L D X x, (y ∈ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = (2*L : ℕ)) ∧ (y ∉ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = 0) := by
  sorry
end ArithmeticThetaPalomarSplit515
