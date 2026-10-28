module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
elab "matcher2087" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
macro "rc":command=> `(run_cmd Lean.modifyEnv fun env=> Lean.EnvExtension.setState matcher2087 (Lean.Meta.auxLemmasExt.setState env {}) {})
macro "sc" es:term:command=> `(run_cmd do
  for n in $es do
    let some c:=(← Lean.getEnv).find? n | throwError "seed"
    Lean.modifyEnv fun e=> Lean.Meta.auxLemmasExt.modifyState e fun s=> { s with lemmas:=s.lemmas.insert { type:=c.type,isPrivate:=false,defeq:=false } (n,c.levelParams) })
elab "ec" n:num:command=> do
  let ss:=(← Lean.Elab.Command.getScopes).take n.getNat
  let nm:=ss.reverse.foldl (fun acc s=> Lean.Name.str acc s.header) Lean.Name.anonymous
  Lean.Elab.Command.elabCommand (← `(end $(Lean.mkIdent nm)))
noncomputable section
universe u v
open _root_ renaming CommRing → z0, Field → z1, CharZero → z2, WeierstrassCurve → z3, PowerSeries → z4, LaurentSeries → z5, MvPolynomial → z6, PresheafOfModules → z8, SheafOfModules → z9, CommRingCat → z10, LinearMap → z11, ModuleCat → z12, AddMonoidHom → z13, RingHom → z14, IsDomain → z15, IsIntegrallyClosed → z16, IsNoetherianRing → z17, IsAlgClosed → z18, Finsupp → z19, SetLike → z20, Submodule → z21, FractionRing → z22, HomogeneousIdeal → z23, HomogeneousLocalization → z24, IsUnit → z25, IsScalarTower → z26, AddSubgroupClass → z27, AddSubmonoidClass → z28, Algebra → z29, Nonempty → z30
open CategoryTheory renaming MonoidalCategory → z7
open AlgebraicGeometry renaming Scheme → zS
open AlgebraicGeometry.Scheme.Modules renaming pullback → zPB, pullbackComp → zPC, pullbackPushforwardAdjunction → zPA, pushforward → zPF open CommRingCat renaming of → zCR, ofHom → zCH open Ideal.Quotient renaming mk → zQM open PresheafOfModules renaming sheafificationAdjunction → zSA, sheafification → zSF open WeierstrassCurve renaming Projective → zWP open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DirectSum HomogeneousLocalization MonoidalCategory MvPolynomial Opposite TopologicalSpace
set_option hygiene false
set_option quotPrecheck false
local notation "vA"=>ArithmeticThetaLocalWeierstrassR0203.Base local notation "vB"=>X.Modules local notation "vC"=>D.atlas.quotient.ring local notation "vD"=>W.toProjective local notation "vE"=>zS.Modules.pullbackLocalSection local notation "vF"=>ArithmeticThetaFullLevelCoverR0175.FullLevel local notation "vG"=>RingCat.carrier local notation "vH"=>X.Opens local notation "vI"=>A.quotient.ring local notation "vJ"=>D.quotient.inclusion local notation "vK"=>Spec.map local notation "vL"=>ArithmeticThetaCompactifiedDifferentialR0145.relativeD local notation "vM"=>H.line local notation "vO"=>D.atlas.descent.family local notation "vP"=>Z.projection local notation "vQ"=>X.germToFunctionField local notation "vR"=>E.projection local notation "vS"=>X.space local notation "vT"=>ArithmeticThetaTateSeries.tateX local notation "vU"=>ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection local notation "vV"=>A.descent.family.curve local notation "vW"=>D.atlas.descent.family.curve local notation "vX"=>A.level.projection local notation "vY"=>GoodReductionJacobian.schemeHomOverComp local notation "vZ"=>A.descent.family.projection local notation "wA"=>RingCat.instCategory local notation "wB"=>Y.Modules local notation "wC"=>X.PresheafOfModules local notation "wD"=>quotient.target local notation "wE"=>X.functionField local notation "wF"=>X.inclusion local notation "wG"=>E.law.schemeNsmul local notation "wH"=>E.curve local notation "wI"=>Polynomial.X local notation "wJ"=>G.schemeNsmul local notation "wK"=>Set.range local notation "wL"=>G.nsmul local notation "wM"=>TopologicalSpace.Opens.map local notation "wN"=>X.presheaf.map local notation "wO"=>z3.DrinfeldGlobal.yOverZ local notation "wP"=>z3.DrinfeldGlobal.xOverZ local notation "wQ"=>ArithmeticThetaUnaryProduct.clearedUnaryTheta local notation "wR"=>A.descent.family.law.one local notation "wS"=>ArithmeticThetaGeometricNormR0150.IsFieldMap local notation "wT"=>zS.Modules.IsInvertible local notation "wU"=>D.atlas local notation "wV"=>ArithmeticThetaGeometricNormR0150.fieldNorm local notation "wW"=>X.IdealSheafData local notation "wX"=>RingCat.instConcreteCategoryRingHomCarrier local notation "wY"=>P544.idealModule local notation "xA"=>gX.kaehlerPresheaf.obj local notation "xB"=>Y.functionField local notation "xC"=>Y.Opens local notation "xD"=>Q.quotient.ring local notation "xE"=>gX.kaehler local notation "xF"=>ArithmeticThetaRelativeKatoR0169.Curve local notation "xG"=>ArithmeticThetaBoundaryHodgeR0182.Test local notation "xH"=>C.map local notation "xI"=>Opposite.op local notation "xJ"=>F.curve local notation "xK"=>ArithmeticThetaOpenHodgeR0180.Test local notation "xL"=>zS.Modules.Hom.app local notation "xM"=>quotient.ring local notation "xN"=>i.val local notation "xO"=>Nat.instAddMonoid local notation "xP"=>Ideal.span local notation "xQ"=>ArithmeticThetaTateSeries.tateY local notation "xR"=>relation.hom local notation "xS"=>RingCat.ring local notation "xT"=>Polynomial.C
local notation "qA"=>(structureMap R W) local notation "qB"=>(LegendreRing k) local notation "qC"=>(Curve R W) local notation "qD"=>(TateCurve k L) local notation "qE"=>(levelFamily k L A) local notation "qF"=>(b≫Q.inclusion) local notation "qG"=>(origin R W) local notation "qH"=>(legendre k) local notation "qI"=>(xI U) local notation "qJ"=>(E.law.one (𝟙 _)) local notation "qK"=>(hodge k L D X x H) local notation "qL"=>(projModelGradingCR V) local notation "qM"=>(projModelGradingCR W) local notation "qN"=>(Curve F W)
local notation "T0(" X ")"=> (@AlgebraicGeometry.PresheafedSpace.carrier z10 z10.instCategory (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace z10 z10.instCategory (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace (AlgebraicGeometry.Scheme.toLocallyRingedSpace X)))) local notation "T2"=> (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
local notation "T7"=> (@z19 T2 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) local notation "T8(" R "," inst ")"=> (@CommSemiring.toSemiring R (@z0.toCommSemiring R inst))
local notation "T20(" R "," inst ")"=> (@AddMonoidAlgebra.instAddCommMonoid R T7 T8(R,inst)) local notation "T17(" R "," inst ")"=> (@AddMonoidAlgebra.instModule R R T7 T8(R,inst) T8(R,inst) (@Semiring.toModule R T8(R,inst)))
local notation "T5(" R "," inst ")"=> (@z6 T2 R (@z0.toCommSemiring R inst)) local notation "T28(" R "," inst ")"=> (@z21 R T5(R,inst) T8(R,inst) T20(R,inst) T17(R,inst))
local notation "T11"=> (@z19.instAddMonoid T2 Nat xO) local notation "T22(" R "," inst ")"=> (@AddMonoidAlgebra.semiring R T7 T8(R,inst) T11)
local notation "T24(" R "," inst ")"=> (@z21.setLike R T5(R,inst) T8(R,inst) T20(R,inst) T17(R,inst)) local notation "T1(" R "," W "," inst ")"=> (@z23.toIdeal Nat T28(R,inst) T5(R,inst) T22(R,inst) T24(R,inst) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1 R inst) (@z6.homogeneousSubmodule T2 R (@z0.toCommSemiring R inst)) instDecidableEqNat xO (@z6.gradedAlgebra T2 R (@z0.toCommSemiring R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR R inst (@z3.toProjective R W)))
local notation "T9(" X ")"=> (@TopologicalSpace.Opens (TopCat.carrier T0(X)) (TopCat.str T0(X))) local notation "T6(" X ")"=> (@Preorder.smallCategory T9(X) (@PartialOrder.toPreorder T9(X) (@TopologicalSpace.Opens.instPartialOrder (TopCat.carrier T0(X)) (TopCat.str T0(X)))))
local notation "T13(" X ")"=> (@CategoryTheory.Functor (Opposite T9(X)) (@CategoryTheory.Category.opposite T9(X) T6(X)) RingCat wA) local notation "T18(" X ")"=> (@CategoryTheory.Functor.category (Opposite T9(X)) (@CategoryTheory.Category.opposite T9(X) T6(X)) RingCat wA)
local notation "T19(" X ")"=> (@Opens.grothendieckTopology (TopCat.carrier T0(X)) (TopCat.str T0(X))) local notation "T3(" X ")"=> (@CategoryTheory.ObjectProperty.FullSubcategory.obj T13(X) T18(X) (@CategoryTheory.Presheaf.IsSheaf T9(X) T6(X) RingCat wA T19(X)) (AlgebraicGeometry.Scheme.ringCatSheaf X))
local notation "T16(" R "," inst ")"=> (@z29.toSMul R T5(R,inst) (@z0.toCommSemiring R inst) T22(R,inst) (@AddMonoidAlgebra.algebra R R T7 (@z0.toCommSemiring R inst) T8(R,inst) (@z29.id R (@z0.toCommSemiring R inst)) T11)) local notation "T32(" R "," inst ")"=> (@AddMonoidAlgebra.ring R T7 (@z0.toRing R inst) T11)
local notation "T4(" R "," W "," inst ")"=> (@z21.Quotient.module' T5(R,inst) T5(R,inst) T32(R,inst) (@AddMonoidAlgebra.addCommGroup R T7 (@z0.toRing R inst)) (@Semiring.toModule T5(R,inst) T22(R,inst)) R T8(R,inst) T16(R,inst) (@z6.instModuleSelf T2 R inst) (@WeierstrassProjModel.kw_lrComul_tensorProj._proof_1 R inst) T1(R,W,inst)) local notation "T21(" R "," inst ")"=> (@AddMonoidAlgebra.commRing R T7 inst (@z19.instAddCommMonoid T2 Nat Nat.instAddCommMonoid))
local notation "T10(" R "," W "," inst ")"=> (@z21.Quotient.addCommGroup T5(R,inst) T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst)) (@Ring.toAddCommGroup T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst))) (@Semiring.toModule T5(R,inst) (@Ring.toSemiring T5(R,inst) (@z0.toRing T5(R,inst) T21(R,inst)))) T1(R,W,inst)) local notation "T12(" R "," W "," inst ")"=> (@WeierstrassProjModel.ProjModelRingCR R inst (@z3.toProjective R W))
local notation "T14(" R "," W "," inst ")"=> (@z21.Quotient.addCommGroup T5(R,inst) T5(R,inst) T32(R,inst) (@AddMonoidAlgebra.addCommGroup R T7 (@z0.toRing R inst)) (@Semiring.toModule T5(R,inst) T22(R,inst)) T1(R,W,inst)) local notation "T15(" R "," inst ")"=> (@Ring.toSemiring T5(R,inst) T32(R,inst))
local notation "T23(" R "," inst ")"=> (@OfNat.ofNat R (nat_lit 0) (@Zero.toOfNat0 R (@MulZeroClass.toZero R (@instMulZeroClassOfSemiring R T8(R,inst))))) local notation "T25(" X ")"=> (@CategoryTheory.CategoryStruct.id T13(X) (@CategoryTheory.Category.toCategoryStruct T13(X) T18(X)) T3(X))
local notation "T26"=> (@Semiring.toNonAssocSemiring (vG S) (@Ring.toSemiring (vG S) (xS S))) local notation "T27"=> (@Semiring.toNonAssocSemiring (vG Y) (@Ring.toSemiring (vG Y) (xS Y)))
local notation "T29(" R ")"=> (@Semiring.toNonAssocSemiring (vG R) (@Ring.toSemiring (vG R) (xS R))) local notation "T30(" X ")"=> (@Semiring.toNonAssocSemiring (vG X) (@Ring.toSemiring (vG X) (xS X)))
set_option quotPrecheck true
set_option hygiene true
set_option hygiene false
set_option quotPrecheck false
 local notation "q1"=>(Compactification k L D)
local notation "q2"=>(algebraMap (z4 k) (z5 k))
local notation "q4"=>((V.disk (closedPoint k))) local notation "q5"=>((Component k L D X x))
local notation "q6"=>((canonicalDivisorData k L D X x divisor effective normal)) local notation "q7"=>((𝟙 X.ringCatSheaf.obj))
local notation "q8"=>((algebraMap R (z22 R))) local notation "q9"=>(Curve (z5 k) (qD))
local notation "q10"=>((@Ring.toSemiring R (@z0.toRing R inst))) local notation "q11"=>(vK (zCH (algebraMap A B)))
local notation "q12"=>(Compactification k (level N) D) local notation "q13"=>(IsLocallyNoetherian X)
local notation "q14"=>(projModelGradingCR vD) local notation "q15"=>((@z0.toCommSemiring R inst))
local notation "q16"=>((AddCommGrpCat.carrier x2)) local notation "q17"=>((AddCommGrpCat.carrier x1))
local notation "q18"=>((AddCommGrpCat.carrier Y)) local notation "q19"=>((AddCommGrpCat.carrier X))
local notation "q20"=>(ArithmeticThetaRelativeDiscriminantR0171.Base R) local notation "q21"=>((universalFamily k L A))
local notation "q22"=>(preDecompose 𝒜 I ℬ hmem a) local notation "q23"=>(Extension k (level N) D X)
local notation "q24"=>(z9.unit X.ringCatSheaf) local notation "q25"=>(DiskTest k (level N) D X)
local notation "q26"=>(((zPB xH).obj J.line)) local notation "q27"=>(LevelData k (level N))
local notation "q28"=>(quotGradingSubmodule 𝒜 I) local notation "q29"=>((zPB V.disk).obj vM)
local notation "q30"=>((Component k (level N) D X q4)) local notation "q31"=>(vA xD)
local notation "q32"=>(z6 (Fin 3) R) local notation "q33"=>(Hodge (z5 k) (qD))
local notation "q34"=>(inclusion k (level N) D X q4) local notation "q35"=>((wY E.zero.ker))
local notation "q36"=>(@z14.instFunLike (vG X) (vG Y) T30(X) T27) local notation "q37"=>(IsIntegral (qC))
local notation "q38"=>((inclusion≫vX)) local notation "q39"=>((z6.homogeneousSubmodule (Fin N) S))
local notation "q40"=>(IsLocallyNoetherian (qC)) local notation "q41"=>(pieceHom 𝒜 I ℬ hmem)
local notation "q42"=>(gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))) local notation "q43"=>(z3 R)
local notation "q44"=>(vA l) local notation "q45"=>(vA k)
local notation "q46"=>(@z14 (vG R) (vG S) T29(R) T26) local notation "q47"=>((hodge vO))
local notation "q48"=>((qC).presheaf.obj (xI U.1)) local notation "q49"=>(IsIntegral (GenericCurve R W))
local notation "q50"=>((zPB T.disk).obj vM) local notation "q51"=>((qC).presheaf.obj (qI))
local notation "q52"=>((baseMap S R C.scalar)) local notation "q53"=>((z9.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom))
local notation "q54"=>((Base vI)) local notation "q55"=>(IsLocallyNoetherian (GenericCurve R W))
local notation "q56"=>(tensorPower vS vM (weight N)) local notation "q57"=>(schemeHomOverComp ψ hψ x)
local notation "q58"=>(vF R W G L (𝟙 (Base R))) local notation "q59"=>((zS.ΓSpecIso (zCR A)))
local notation "q60"=>((Classical.choice hV.down)) local notation "q61"=>(schemeHomOverComp ψ hψ (mul t x y))
local notation "q62"=>(J.presheaf.map (homOfLE (show p ⁻¹ᵁ U≤⊤ from le_top)).op t) local notation "q63"=>(wS (wJ d) φ)
local notation "q64"=>((@AddCommGroup.toAddCommMonoid T12(R,W,inst) T14(R,W,inst))) local notation "q65"=>((@AddCommGroup.toAddCommMonoid T12(R,W,inst) T10(R,W,inst)))
local notation "q66"=>(SchemeHomOver t (qA)) local notation "q67"=>((@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
local notation "q68"=>((@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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
ec 1
section SubmoduleVersion
variable {ι R A:Type*} variable [z0 R] [z0 A] [z29 R A] variable (𝒜:ι→ z21 R A) variable (I:Ideal A)
def quotGradingSubmodule(i:ι):z21 R (A ⧸ I):=(𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff{i:ι}{x:A ⧸ I}:x∈q28 i↔∃ a∈𝒜 i,zQM I a=x:=by sorry
lemma mk_mem_quotGradingSubmodule{i:ι}{a:A}(ha:a∈𝒜 i):zQM I a∈q28 i:=(mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a,ha,rfl⟩
instance quotGradingSubmoduleGradedMonoid[AddMonoid ι][z20.GradedMonoid 𝒜]:z20.GradedMonoid (q28):=by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra(hI:I.IsHomogeneous 𝒜):GradedAlgebra (q28):=gradedRingOfImages 𝒜 I (q28) (fun _ _ ha=> mk_mem_quotGradingSubmodule 𝒜 I ha) (fun _ _ hb=> (mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous(J:z23 𝒜):GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal):=quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
ec 1
ec 1 open HomogeneousIdealQuotientGrading
section rc variable {F:Type*} [z0 F]
theorem ProjWeierstrassCubicPrime.isHomogeneous_polynomial(V:zWP F):V.polynomial.IsHomogeneous 3:=by sorry end
open ProjWeierstrassCubicPrime namespace WeierstrassProjModel rc
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R:Type*} [z0 R]
theorem span_polynomial_isHomogeneousCR(V:zWP R):(xP {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R):=by sorry
def projModelHomogeneousIdealCR(V:zWP R):z23 (homogeneousSubmodule (Fin 3) R):=⟨xP {V.polynomial},span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal(V:zWP R):(projModelHomogeneousIdealCR V).toIdeal=xP {V.polynomial}:=rfl
abbrev ProjModelRingCR(V:zWP R):Type _:=q32 ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR(V:zWP R):ℕ→ z21 R (ProjModelRingCR V):=quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR(V:zWP R):zS:=Proj (qL)
def projModelStrCR(V:zWP R):Proj (qL)⟶Spec (zCR R):=Proj.toSpecZero (qL)≫vK (zCH (algebraMap R ((qL) 0)))
ec 1 variable (R:Type u) [CommRing R]
section ZeroSection
variable (W:z3 R)
open MvPolynomial in
theorem kw_mk_X1_mem_one_CR:zQM (projModelHomogeneousIdealCR vD).toIdeal (X 1:q32)∈q14 1:=mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
theorem kw_lrComul_tensorProj._proof_1.{u_1}:∀ {R:Type u_1} [inst:z0 R],@z26 R T5(R,inst) T5(R,inst) T16(R,inst) (@instSMulOfMul T5(R,inst) (@Distrib.toMul T5(R,inst) (@instDistribOfSemiring T5(R,inst) T22(R,inst)))) T16(R,inst):=by sorry
theorem kw_lrChart_aux._proof_1.{u_1}:∀ {R:Type u_1} [inst:z0 R] (W:q43),@z27 (@z21 R T12(R,W,inst) q10 q64 T4(R,W,inst)) T12(R,W,inst) (@AddGroup.toSubNegMonoid T12(R,W,inst) (@AddCommGroup.toAddGroup T12(R,W,inst) T14(R,W,inst))) (@z21.setLike R T12(R,W,inst) q10 q64 T4(R,W,inst)):=by sorry
theorem kw_lrChart_aux._proof_2.{u_1}:∀ {R:Type u_1} [inst:z0 R] (W:q43),@z27 (@z21 R T12(R,W,inst) q10 q65 T4(R,W,inst)) T12(R,W,inst) (@AddGroup.toSubNegMonoid T12(R,W,inst) (@AddCommGroup.toAddGroup T12(R,W,inst) T10(R,W,inst))) (@z21.setLike R T12(R,W,inst) q10 q65 T4(R,W,inst)):=by sorry
theorem kw_lrSixU_toE._proof_1:@LT.lt Nat (@Preorder.toLT Nat (@PartialOrder.toPreorder Nat Nat.instPartialOrder)) (@OfNat.ofNat Nat (nat_lit 0) (@Zero.toOfNat0 Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))) (@OfNat.ofNat Nat (nat_lit 1) (@One.toOfNat1 Nat Nat.instOne)):=by sorry
theorem kw_lrAdd_comulHom._proof_2.{u_1}:∀ {R:Type u_1} [inst:z0 R],@z28 T28(R,inst) T5(R,inst) (@AddMonoid.toAddZeroClass T5(R,inst) (@AddCommMonoid.toAddMonoid T5(R,inst) T20(R,inst))) T24(R,inst):=by sorry
theorem kw_lrAdd_comulHom._proof_3.{u_1}:∀ {R:Type u_1} [inst:z0 R] (W:q43),@Ideal.IsTwoSided T5(R,inst) (@CommSemiring.toSemiring T5(R,inst) (@z0.toCommSemiring T5(R,inst) T21(R,inst))) (@z23.toIdeal Nat T28(R,inst) T5(R,inst) T22(R,inst) T24(R,inst) (@WeierstrassProjModel.kw_lrAdd_comulHom._proof_2 R inst) (@z6.homogeneousSubmodule T2 R q15) instDecidableEqNat xO (@z6.gradedAlgebra T2 R q15) (@WeierstrassProjModel.projModelHomogeneousIdealCR R inst (@z3.toProjective R W))):=by sorry
theorem kw_lrAddNegDiag_negSubstGen._proof_1:@NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) q67 q68):=by sorry
theorem kwYEvalRingHom._proof_2.{u_1}:∀ (R:Type u_1) [inst:z0.{u_1} R] (W:q43) (a:@z6.{0,u_1} T2 R q15) (ha:@Membership.mem.{u_1,u_1} T5(R,inst) (@Ideal.{u_1} T5(R,inst) T15(R,inst)) (@z20.instMembership.{u_1,u_1} (@Ideal.{u_1} T5(R,inst) T15(R,inst)) T5(R,inst) (@z21.setLike.{u_1,u_1} T5(R,inst) T5(R,inst) T15(R,inst) (@Semiring.toAddCommMonoid.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toModule.{u_1} T5(R,inst) T15(R,inst)))) T1(R,W,inst) a),@Eq.{u_1+1} R (@DFunLike.coe.{u_1+1,u_1+1,u_1+1} (@z14.{u_1,u_1} T5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R T8(R,inst))) T5(R,inst) (fun (x:@z6.{0,u_1} T2 R q15)=> R) (@z14.instFunLike.{u_1,u_1} T5(R,inst) R (@Semiring.toNonAssocSemiring.{u_1} T5(R,inst) T15(R,inst)) (@Semiring.toNonAssocSemiring.{u_1} R T8(R,inst))) (@z6.eval.{u_1,0} R T2 q15 (@Matrix.vecCons.{u_1} R q67 T23(R,inst) (@Matrix.vecCons.{u_1} R q68 (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R (@AddGroupWithOne.toAddMonoidWithOne.{u_1} R (@Ring.toAddGroupWithOne.{u_1} R (@z0.toRing.{u_1} R inst)))))) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) T23(R,inst) (@Matrix.vecEmpty.{u_1} R))))) a) T23(R,inst):=by sorry
sc [``kw_lrComul_tensorProj._proof_1,``kw_lrChart_aux._proof_1,``kw_lrChart_aux._proof_2,``kw_lrSixU_toE._proof_1,``kw_lrAdd_comulHom._proof_2,``kw_lrAdd_comulHom._proof_3,``kw_lrAddNegDiag_negSubstGen._proof_1,`WeierstrassProjModel.kwYEvalRingHom._proof_2]
open MvPolynomial in
def kwYEvalRingHom:ProjModelRingCR vD→+*R:=
  Ideal.Quotient.lift _ (z6.eval ![(0:R),1,0]) fun a ha=> by
    refine (Ideal.span_le.mpr ?_:xP _≤z14.ker _)
      (projModelHomogeneousIdealCR_toIdeal vD ▸ ha)
    simp only [Set.singleton_subset_iff,z20.mem_coe,z14.mem_ker]
    exact z3.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1:kwYEvalRingHom R W (zQM _ (X 1:q32))=1:=by sorry
def kwYChartEval:z24.Away (q14) (zQM _ (z6.X 1:q32))→+*R:=(IsLocalization.Away.lift (g:=kwYEvalRingHom R W) (zQM _ (z6.X 1:q32)) (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (z24.Away (q14) (zQM _ (z6.X 1:q32))) (Localization.Away (zQM (projModelHomogeneousIdealCR vD).toIdeal (z6.X 1:q32))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap:(kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR vD))=z14.id R:=by sorry
theorem kwYChartEval_section:(kwYChartEval R W).comp ((z24.fromZeroRingHom (q14) _).comp (algebraMap R (q14 0)))=z14.id R:=by sorry
def kwZeroSect:sh (𝟙 (Spec (zCR R))) (projModelStrCR vD):=
  ⟨vK (zCH (kwYChartEval R W))≫
    Proj.awayι (q14) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR,Category.assoc]
    rw [← Category.assoc (Proj.awayι ..),Proj.awayι_toSpecZero,← Spec.map_comp,
      ← Spec.map_comp,← z10.ofHom_comp,← z10.ofHom_comp,
      kwYChartEval_section,z10.ofHom_id,Spec.map_id]⟩
ec 1
def schemeHomOverComp{B T' T A:Scheme.{u}}{t:T⟶B}{t':T'⟶B}{f:A⟶B}(ψ:T'⟶T)(hψ:ψ≫t=t')(x:sh t f):sh t' f:=
  ⟨ψ≫x.1,by rw [Category.assoc,x.2,hψ]⟩
structure RelativeGroupLaw(R:Type u)[z0 R]{A:zS.{u}}(f:A⟶Spec (zCR R)) where (mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f→ sh t f) (one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f) (inv:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f) (mul_assoc:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y z:sh t f),mul t (mul t x y) z=mul t x (mul t y z)) (one_mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (one t) x=x) (mul_one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t x (one t)=x) (inv_mul_cancel:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (inv t x) x=one t) (mul_natural:∀ {T T':zS.{u}} (t:T⟶Spec (zCR R)) (t':T'⟶Spec (zCR R)) (ψ:T'⟶T) (hψ:ψ≫t=t') (x y:sh t f),q61=mul t' (q57) (schemeHomOverComp ψ hψ y))
ec 1 open WeierstrassProjModel namespace ArithmeticThetaRelativeKatoR0169 rc variable (R:Type u) [z0 R]
abbrev Curve(W:z3 R):zS.{u}:=projModelCR vD
def structureMap(W:z3 R):Curve R W⟶Spec (zCR R):=projModelStrCR vD
def origin(W:z3 R):Spec (zCR R)⟶Curve R W:=(kwZeroSect R W).val
abbrev Law(W:z3 R):=WeierstrassProjModel.RelativeGroupLaw R (qA)
def IsOriginLaw(W:z3 R)(G:Law R W):Prop:=(∀ {V:zS.{u}} (t:V⟶Spec (zCR R)),(G.one t).val=t≫origin R W)∧(∀ {V:zS.{u}} (t:V⟶Spec (zCR R)) (x y:q66),G.mul t x y=G.mul t y x)
ec 1 open ArithmeticThetaRelativeKatoR0169
section rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
def WeierstrassProjModel.RelativeGroupLaw.nsmul(G:RelativeGroupLaw R f){T:zS.{u}}(t:T⟶Spec (zCR R))(n:ℕ)(x:sh t f):sh t f:=Nat.rec (G.one t) (fun _ ih=> G.mul t ih x) n end
namespace GoodReductionJacobian rc
def schemeHomOverComp{B T' T A:Scheme.{u}}{t:T⟶B}{t':T'⟶B}{f:A⟶B}(ψ:T'⟶T)(hψ:ψ≫t=t')(x:sh t f):sh t' f:=
  ⟨ψ≫x.1,by rw [Category.assoc,x.2,hψ]⟩
structure RelativeGroupLaw(R:Type u)[z0 R]{A:zS.{u}}(f:A⟶Spec (zCR R)) where (mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f→ sh t f) (one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f) (inv:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)),sh t f→ sh t f) (mul_assoc:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y z:sh t f),mul t (mul t x y) z=mul t x (mul t y z)) (one_mul:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (one t) x=x) (mul_one:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t x (one t)=x) (inv_mul_cancel:∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x:sh t f),mul t (inv t x) x=one t) (mul_natural:∀ {T T':zS.{u}} (t:T⟶Spec (zCR R)) (t':T'⟶Spec (zCR R)) (ψ:T'⟶T) (hψ:ψ≫t=t') (x y:sh t f),q61=mul t' (q57) (schemeHomOverComp ψ hψ y))
section rc
def RelativeGroupLaw.IsCommutative{R:Type u}[z0 R]{A:zS.{u}}{f:A⟶Spec (zCR R)}(G:RelativeGroupLaw R f):Prop:=∀ {T:zS.{u}} (t:T⟶Spec (zCR R)) (x y:sh t f),G.mul t x y=G.mul t y x end
ec 1 namespace GoodReductionJacobian.RelativeGroupLaw rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
def nsmul(G:RelativeGroupLaw R f){T:zS.{u}}(t:T⟶Spec (zCR R))(n:ℕ)(x:sh t f):sh t f:=Nat.rec (G.one t) (fun _ ih=> G.mul t ih x) n
abbrev idPoint:sh f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul(G:RelativeGroupLaw R f)(n:ℕ):A⟶A:=(wL f n idPoint).1
ec 2
section rc
abbrev ArithmeticThetaRelativeDiscriminantR0171.Base(R:Type u)[z0 R]:=Spec (zCR R) end
open ArithmeticThetaRelativeDiscriminantR0171 namespace ArithmeticThetaFullLevelCoverR0175 rc variable (R:Type u) [z0 R] (W:z3 R) (G:Law R W)
structure FullLevel(L:ℕ){T:zS.{u}}(t:T⟶Base R) where (x:q66) (y:q66) (killed_x:wL t L x=G.one t) (killed_y:wL t L y=G.one t) (avoids:∀ i j:Fin L,xN≠0∨j.val≠0→ Disjoint (wK (G.mul t (wL t xN x) (wL t j.val y)).val) (wK (qG)))
structure LevelScheme(L:ℕ) where (space:zS.{u}) (projection:space⟶Base R) (level:vF R W G L projection)
def Represents{L:ℕ}(D:LevelScheme R W G L):Prop:=∀ (T:zS.{u}) (t:T⟶Base R) (A:vF R W G L t),∃! q:sh t D.projection,q.val≫D.level.x.val=A.x.val∧q.val≫D.level.y.val=A.y.val
def levelDegree(L:ℕ):ℕ:=Nat.card ((ZMod L × ZMod L) ≃+(ZMod L × ZMod L))
ec 1 open ArithmeticThetaFullLevelCoverR0175 namespace ArithmeticThetaLegendreAtlasR0176 rc
abbrev LegendreRing(k:Type u)[z1 k]:=Localization.Away (wI*(wI - 1):Polynomial k)
def parameter(k:Type u)[z1 k]:LegendreRing k:=algebraMap (Polynomial k) (qB) wI
def legendre(k:Type u)[z1 k]:z3 (qB) where
  a₁:=0
  a₂:=-(parameter k+1)
  a₃:=0
  a₄:=parameter k
  a₆:=0
def legendreBaseMap(k:Type u)[z1 k]:Base (qB)⟶Base k:=vK (zCH (algebraMap k (qB)))
structure SignAction(R:Type u)[z0 R](W:z3 R)(G:Law R W){L:ℕ}(Z:LevelScheme R W G L) where (map:Z.space⟶Z.space) (over_eq:map≫vP=vP) (square:map≫map=𝟙 _) (x_eq:map≫Z.level.x.val=(G.inv vP Z.level.x).val) (y_eq:map≫Z.level.y.val=(G.inv vP Z.level.y).val) (free:IsEmpty (equalizer map (𝟙 Z.space):zS.{u}))
structure SignQuotient(k:Type u)[z1 k]{X:zS.{u}}(p:X⟶Base k)(σ:X⟶X) where (ring:Type u) [commRing:z0 ring] [algebra:z29 k ring] (q:X⟶Base ring) (over_eq:q≫vK (zCH (algebraMap k ring))=p) (invariant:σ≫q=q) (finite:IsFinite q) (etale:Etale q) (surjective:Surjective q) (degree:∀ x,q.finrank x=2) (smooth:SmoothOfRelativeDimension 1 (vK (zCH (algebraMap k ring)))) (relation:(X ⨿ X)≅pullback q q) (left_fst:coprod.inl≫xR≫pullback.fst q q=𝟙 X) (left_snd:coprod.inl≫xR≫pullback.snd q q=𝟙 X) (right_fst:coprod.inr≫xR≫pullback.fst q q=𝟙 X) (right_snd:coprod.inr≫xR≫pullback.snd q q=σ) (universal:∀ (T:zS.{u}) (a:X⟶T),σ≫a=a→ ∃! b:Base ring⟶T,q≫b=a)
attribute [instance] SignQuotient.commRing SignQuotient.algebra
abbrev coverCurve(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback (qA) vP
abbrev coverToCurve(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback.fst (qA) vP
abbrev coverToLevel(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L):=pullback.snd (qA) vP
def coverSection(R:Type u)[z0 R](W:z3 R){G:Law R W}{L:ℕ}(Z:LevelScheme R W G L)(s:sh vP (qA)):Z.space⟶coverCurve R W Z:=
  pullback.lift s.val (𝟙 _) (by simpa using s.property)
structure EllipticFamily(S:Type u)[z0 S] where (curve:zS.{u}) (projection:curve⟶Base S) (law:GoodReductionJacobian.RelativeGroupLaw S projection) (commutative:law.IsCommutative) (proper:IsProper projection) (smooth:SmoothOfRelativeDimension 1 projection) (connected:GeometricallyConnected projection)
structure FamilyLevel(S:Type u)[z0 S](E:EllipticFamily S)(L:ℕ) where (x:sh (𝟙 (Base S)) vR) (y:sh (𝟙 (Base S)) vR) (killed_x:x.val≫wG L=(qJ).val) (killed_y:y.val≫wG L=(qJ).val) (avoids:∀ i j:Fin L,xN≠0∨j.val≠0→ Disjoint (wK (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) xN x) (E.law.nsmul (𝟙 _) j.val y)).val) (wK (qJ).val))
def FamilyRigid(S:Type u)[z0 S](E:EllipticFamily S){L:ℕ}(M:FamilyLevel S E L):Prop:=∀ e:wH≅wH,e.hom≫vR=vR→ (qJ).val≫e.hom=(qJ).val→ M.x.val≫e.hom=M.x.val→ M.y.val≫e.hom=M.y.val→ e.hom=𝟙 wH
structure FamilyDescent(k R:Type u)[z1 k][z0 R][z29 k R](W:z3 R)(G:Law R W){L:ℕ}(Z:LevelScheme R W G L)(σ:SignAction R W G Z)(Q:SignQuotient k (vP≫vK (zCH (algebraMap k R))) σ.map) where (family:EllipticFamily Q.ring) (comparison:coverCurve R W Z⟶family.curve) (cartesian:IsPullback comparison (coverToLevel R W Z) family.projection Q.q) (origin_eq:coverSection R W Z (G.one vP)≫comparison=Q.q≫(family.law.one (𝟙 _)).val) (action:coverCurve R W Z⟶coverCurve R W Z) (action_level:action≫coverToLevel R W Z=coverToLevel R W Z≫σ.map) (action_curve:action≫coverToCurve R W Z=(G.inv (coverToLevel R W Z≫vP) ⟨coverToCurve R W Z,pullback.condition⟩).val) (invariant:action≫comparison=comparison)
structure LegendreAtlas(k:Type u)[z1 k](L:ℕ) where (law:Law (qB) (qH)) (originLaw:IsOriginLaw (qB) (qH) law) (level:LevelScheme (qB) (qH) law L) (represents:Represents (qB) (qH) law level) (sign:SignAction (qB) (qH) law level) (quotient:SignQuotient k (level.projection≫legendreBaseMap k) sign.map) (descent:FamilyDescent k (qB) (qH) law level sign quotient) (marking:FamilyLevel xM descent.family L) (rigid:FamilyRigid xM descent.family marking) (x_eq:coverSection (qB) (qH) level level.level.x≫descent.comparison=quotient.q≫marking.x.val) (y_eq:coverSection (qB) (qH) level level.level.y≫descent.comparison=quotient.q≫marking.y.val)
ec 1 open ArithmeticThetaLegendreAtlasR0176 open ArithmeticThetaLegendreAtlasR0176 renaming LegendreAtlas → la
section Chart
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal rc variable {T:Type u} [z0 T] (W:zWP T)
abbrev coord(i:Fin 3):ProjModelRingCR W:=zQM (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem(i:Fin 3):coord W i∈projModelGradingCR W 1:=mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
abbrev ZChartRing:Type u:=Away (qM) (coord W 2)
abbrev zChartι:Spec (zCR (ZChartRing W))⟶projModelCR W:=Proj.awayι (qM) (coord W 2) (coord_mem W 2) one_pos
def xOverZ:ZChartRing W:=
  Away.mk (qM) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ:ZChartRing W:=
  Away.mk (qM) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
ec 2
ec 1 open WeierstrassCurve.DrinfeldGlobal namespace ArithmeticThetaLegendreComparisonR0177 rc
abbrev ChartRing(R:Type u)[z0 R](W:z3 R):=z3.DrinfeldGlobal.ZChartRing vD
def chartInclusion(R:Type u)[z0 R](W:z3 R):Spec (zCR (ChartRing R W))⟶Curve R W:=z3.DrinfeldGlobal.zChartι vD
def chartScalar(R:Type u)[z0 R](W:z3 R):R→+*ChartRing R W:=(Spec.preimage (chartInclusion R W≫structureMap R W)).hom
def HasCoordinates(R:Type u)[z0 R](W:z3 R)(P:Base R⟶Curve R W)(x y:R):Prop:=P≫structureMap R W=𝟙 (Base R)∧∃ χ:ChartRing R W→+*R,P=vK (zCH χ)≫chartInclusion R W∧χ (wP vD)=x∧χ (wO vD)=y
def completedCubic(R:Type u)[z0 R][z29 ℚ R](W:z3 R):Polynomial R:=wI^3+xT (W.a₂+algebraMap ℚ R (1/4)*W.a₁^2)*wI^2+xT (W.a₄+algebraMap ℚ R (1/2)*W.a₁*W.a₃)*wI+xT (W.a₆+algebraMap ℚ R (1/4)*W.a₃^2)
def SplitCubic(R:Type u)[z0 R][z29 ℚ R](W:z3 R)(e:Fin 3→ R):Prop:=(∀ i j,i≠j→ z25 (e i - e j))∧completedCubic R W=∏ i:Fin 3,(wI - xT (e i))
ec 1 open ArithmeticThetaLegendreComparisonR0177 namespace ArithmeticThetaCompatibleLevelR0178 rc variable (k:Type u) [z1 k] [z2 k] (L:ℕ) (A:la k L)
abbrev TwoMarking:=FullLevel (qB) (qH) A.law 2 (𝟙 (Base (qB)))
def CanonicalTwo(B:TwoMarking k L A):Prop:=HasCoordinates (qB) (qH) B.x.val 0 0∧HasCoordinates (qB) (qH) B.y.val 1 0
def CompatibleAt(B:TwoMarking k L A){T:zS.{u}}(a:T⟶A.level.space):Prop:=a≫(A.law.nsmul vX (L/2) A.level.level.x).val=(a≫vX)≫B.x.val∧a≫(A.law.nsmul vX (L/2) A.level.level.y).val=(a≫vX)≫B.y.val
structure CompatibleCover(B:TwoMarking k L A) where (space:zS.{u}) (inclusion:space⟶A.level.space) (openImmersion:IsOpenImmersion inclusion) (closedImmersion:IsClosedImmersion inclusion) (compatible:CompatibleAt k L A B inclusion) (represents:∀ (T:zS.{u}) (a:T⟶A.level.space),CompatibleAt k L A B a↔∃! b:T⟶space,b≫inclusion=a) (finite:IsFinite q38) (etale:Etale q38) (surjective:Surjective q38) (degree:∀ z,(q38).finrank z=levelDegree L/6)
structure CompatibleQuotient(B:TwoMarking k L A)(C:CompatibleCover k L A B) where (sign:C.space⟶C.space) (sign_eq:sign≫C.inclusion=C.inclusion≫A.sign.map) (sign_square:sign≫sign=𝟙 _) (sign_free:IsEmpty (equalizer sign (𝟙 C.space):zS.{u})) (quotient:SignQuotient k (C.inclusion≫vX≫legendreBaseMap k) sign) (inclusion:Base xM⟶Base vI) (cartesian:IsPullback C.inclusion quotient.q A.quotient.q inclusion) (openImmersion:IsOpenImmersion inclusion) (closedImmersion:IsClosedImmersion inclusion) (over_eq:inclusion≫vK (zCH (algebraMap k vI))=vK (zCH (algebraMap k xM)))
ec 1 open ArithmeticThetaCompatibleLevelR0178 open ArithmeticThetaCompatibleLevelR0178 renaming CompatibleCover → cc, CompatibleQuotient → cq, TwoMarking → tm namespace ArithmeticThetaProjectiveEffectivityR0135 rc
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace(S:Type u)[z0 S](N:ℕ):zS.{u}:=AlgebraicGeometry.Proj q39
def projectiveStructure(S:Type u)[z0 S](N:ℕ):projectiveSpace S N⟶Spec (zCR S):=Proj.toSpecZero q39≫vK (zCH (algebraMap S (q39 0)))
ec 1 namespace ArithmeticThetaLevelCompactificationR0179 rc
structure LevelData(k:Type u)[z1 k](L:ℕ) where (atlas:la k L) (two:tm k L atlas) (canonical:CanonicalTwo k L atlas two) (cover:cc k L atlas two) (quotient:cq k L atlas two cover)
variable (k:Type u) [z1 k] (L:ℕ)
abbrev OpenBase(D:LevelData k L):=Base D.quotient.quotient.ring
def openStructure(D:LevelData k L):OpenBase k L D⟶Base k:=vK (zCH (algebraMap k D.quotient.quotient.ring))
structure Compactification(D:LevelData k L) where (space:zS.{u}) (projection:space⟶Base k) (inclusion:OpenBase k L D⟶space) (over_eq:inclusion≫projection=openStructure k L D) (openImmersion:IsOpenImmersion inclusion) (dense:DenseRange inclusion.base) (proper:IsProper projection) (smooth:SmoothOfRelativeDimension 1 projection) (dimension:ℕ) (embedding:space⟶ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)) (closedImmersion:IsClosedImmersion embedding) (embedding_over:embedding≫ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1)=projection)
def boundary(D:LevelData k L)(X:q1):Set vS:=(wK X.inclusion.base)ᶜ
ec 1 open ArithmeticThetaLevelCompactificationR0179 open ArithmeticThetaLevelCompactificationR0179 renaming LevelData → ld, Compactification → cp namespace WeierstrassProjModel.RelativeGroupLaw rc variable {R:Type u} [z0 R] {A:zS.{u}} {f:A⟶Spec (zCR R)}
abbrev idPoint:sh f f:=⟨𝟙 A,Category.id_comp f⟩
def schemeNsmul(G:RelativeGroupLaw R f)(n:ℕ):A⟶A:=(wL f n idPoint).1
ec 2
section rc
structure AlgebraicGeometry.Scheme.Modules.IsInvertible{X:Scheme.{u}}(M:vB):Prop where (exists_trivialization:∀ x:X,∃ (U:vH),x∈U∧z30 ((zPB U.ι).obj M≅z9.unit U.toScheme.ringCatSheaf))
end
namespace AlgebraicGeometry.Scheme.Hom rc variable {A:Type u} [z0 A] {X:zS.{u}} (f:X⟶Spec (zCR A))
def constToPresheaf:(Functor.const (vH)ᵒᵖ).obj (zCR A)⟶X.presheaf where
  app U:=(q59).inv≫f.appLE ⊤ U.unop le_top
  naturality U V i:=by
    simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.id_comp,Category.assoc]
    rw [zS.Hom.appLE_map]
@[reducible] def sectionsAlgebra(U:vH):z29 A Γ(X,U):=(f.constToPresheaf.app (op U)).hom.toAlgebra
def kaehlerPresheaf:wC:=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf
def kaehler:vB:=(zSF q7).obj f.kaehlerPresheaf
def kaehlerToSections(U:vH):(f.kaehlerPresheaf.obj (op U):Type u)→ (Γ(f.kaehler,U):Type u):=fun s=> (((zSA q7).unit.app f.kaehlerPresheaf).app (op U)).hom s
ec 3
section rc variable {X Y:zS.{u}} (φ:X⟶Y) {L:wB} {U:xC}
def AlgebraicGeometry.Scheme.Modules.pullbackLocalSection(s:Γ(L,U)):Γ((Modules.pullback φ).obj L,φ ⁻¹ᵁ U):=((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s end
namespace ArithmeticThetaSheafTensor rc variable (X:zS.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor:z7 wC:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def tensorPresheaf(H K:vB):wC:=H.val ⊗ K.val
def sheafTensor(H K:vB):vB:=(zSF q7).obj (tensorPresheaf X H K)
def tensorUnitMap(H K:vB):tensorPresheaf X H K⟶(sheafTensor X H K).val:=(zSA q7).unit.app _
def tensorSection(H K:vB)(U:vH)(s:Γ(H,U))(t:Γ(K,U)):Γ(sheafTensor X H K,U):=(tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X,U)] t)
ec 1 open ArithmeticThetaSheafTensor
section rc
def ArithmeticThetaTensorPower.tensorPower(X:zS.{u})(H:vB):ℕ→ vB | 0=> q24 | n+1=> sheafTensor X (tensorPower X H n) H
end
open ArithmeticThetaTensorPower open ArithmeticThetaTensorPower renaming tensorPower → tp namespace ArithmeticThetaRelativeDiscriminantR0171 rc
abbrev Hodge(R:Type u)[z0 R](W:z3 R):=(zPB (qG)).obj (qA).kaehler
abbrev HodgePower(R:Type u)[z0 R](W:z3 R)(n:ℕ):=tp (Base R) (Hodge R W) n
def res{X:Scheme.{u}}(F:vB){U V:vH}(h:V≤U)(s:Γ(F,U)):Γ(F,V):=F.presheaf.map (homOfLE h).op s
def IsFrame{X:Scheme.{u}}(F:vB)(U:vH)(s:Γ(F,U)):Prop:=∀ (V:vH) (h:V≤U),Function.Bijective (fun a:X.presheaf.obj (xI V)=> a•res F h s)
def baseMap(R:Type u)[z0 R](S:Type u)[z0 S](ι:R→+*S):Base S⟶Base R:=vK (zCH ι)
ec 1 namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull rc
theorem T0.unitD._proof_1.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.Presheaf.IsLocallyInjective T9(X) T6(X) RingCat wA (fun (R S:RingCat)=> q46) vG (fun (X Y:RingCat)=> q36) wX T19(X) T3(X) T3(X) T25(X):=by sorry
theorem T0.unitD._proof_2.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.Presheaf.IsLocallySurjective T9(X) T6(X) T19(X) RingCat wA (fun (R S:RingCat)=> q46) vG (fun (X Y:RingCat)=> q36) wX T3(X) T3(X) T25(X):=by sorry
theorem T0.unitD._proof_3.{u_1}:∀ {X:AlgebraicGeometry.Scheme.{u_1}},@CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.{u_1,u_1,u_1,u_1+1,u_1,u_1} T9(X) T6(X) T19(X) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory.{u_1} (fun (x1 x2:AddCommGrpCat.{u_1})=> @z13.{u_1,u_1} q17 q16 (@AddZeroClass.toAddZero.{u_1} q17 (@AddMonoid.toAddZeroClass.{u_1} q17 (@SubNegMonoid.toAddMonoid.{u_1} q17 (@AddGroup.toSubNegMonoid.{u_1} q17 (@AddCommGroup.toAddGroup.{u_1} q17 (AddCommGrpCat.str.{u_1} x1)))))) (@AddZeroClass.toAddZero.{u_1} q16 (@AddMonoid.toAddZeroClass.{u_1} q16 (@SubNegMonoid.toAddMonoid.{u_1} q16 (@AddGroup.toSubNegMonoid.{u_1} q16 (@AddCommGroup.toAddGroup.{u_1} q16 (AddCommGrpCat.str.{u_1} x2))))))) AddCommGrpCat.carrier.{u_1} (fun (X Y:AddCommGrpCat.{u_1})=> @z13.instFunLike.{u_1,u_1} q19 q18 (@AddZeroClass.toAddZero.{u_1} q19 (@AddMonoid.toAddZeroClass.{u_1} q19 (@SubNegMonoid.toAddMonoid.{u_1} q19 (@AddGroup.toSubNegMonoid.{u_1} q19 (@AddCommGroup.toAddGroup.{u_1} q19 (AddCommGrpCat.str.{u_1} X)))))) (@AddZeroClass.toAddZero.{u_1} q18 (@AddMonoid.toAddZeroClass.{u_1} q18 (@SubNegMonoid.toAddMonoid.{u_1} q18 (@AddGroup.toSubNegMonoid.{u_1} q18 (@AddCommGroup.toAddGroup.{u_1} q18 (AddCommGrpCat.str.{u_1} Y))))))) AddCommGrpCat.instConcreteCategoryAddMonoidHomCarrier.{u_1}:=by sorry
theorem T0.unitD._proof_4.{u_1}:∀ {X:zS.{u_1}},@CategoryTheory.HasWeakSheafify T9(X) T6(X) T19(X) AddCommGrpCat.{u_1} AddCommGrpCat.instCategory:=by sorry
sc [``T0.unitD._proof_1,``T0.unitD._proof_2,``T0.unitD._proof_3,``T0.unitD._proof_4]
section Main
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hφ:φ≫gY=gX≫q11) (d:ℕ)
include hφ
lemma fac(U:xC):zCH (algebraMap A B)≫q42=gY.constToPresheaf.app (op U)≫φ.app U:=by
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
def kdMap(U:xC):gY.kaehlerPresheaf.obj (op U)⟶(z12.restrictScalars (φ.app U).hom).obj (xA (op (φ ⁻¹ᵁ U))):=z10.KaehlerDifferential.map (fac gY gX φ hφ U)
abbrev unit1(V:vH):xA (op V)⟶gX.kaehler.val.obj (op V):=((zSA q7).unit.app gX.kaehlerPresheaf).app (op V)
omit hφ in
def dK{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C))(V:Z.Opens)(b:Γ(Z,V)):(g.kaehlerPresheaf.obj (op V):Type u):=z10.KaehlerDifferential.d (f:=g.constToPresheaf.app (op V)) b
omit hφ in
lemma kp_map_dK{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C)){V V':Z.Opens}(i:op V⟶op V')(b:Γ(Z,V)):g.kaehlerPresheaf.map i (dK g V b)=dK g V' (Z.presheaf.map i b):=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d g.constToPresheaf i b
omit hφ in
lemma kp_hom_ext{C:Type u}[z0 C]{Z:zS.{u}}(g:Z⟶Spec (zCR C))(V:Z.Opens){M:z12 Γ(Z,V)}{α β:g.kaehlerPresheaf.obj (op V)⟶M}(h:∀ b:Γ(Z,V),α (dK g V b)=β (dK g V b)):α=β:=z10.KaehlerDifferential.ext h
omit hφ in
lemma map_unit1{V V':vH}(j:op V⟶op V')(x:xA (op V)):gX.kaehler.val.map j (unit1 gX V x)=unit1 gX V' (gX.kaehlerPresheaf.map j x):=(z8.naturality_apply ((zSA q7).unit.app gX.kaehlerPresheaf) j x).symm
omit hφ in
lemma φ_naturality_apply{U U':xC}(i:op U⟶op U')(b:Γ(Y,U)):wN ((wM φ.base).map i.unop).op (φ.app U b)=φ.app U' (Y.presheaf.map i b):=(CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm
def k1app(U:xC):gY.kaehlerPresheaf.obj (op U)⟶((zPF φ).obj xE).val.obj (op U):=kdMap gY gX φ hφ U≫(z12.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))
lemma k1app_dK(U:xC)(b:Γ(Y,U)):k1app gY gX φ hφ U (dK gY U b)=unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)):=by
  show unit1 gX (φ ⁻¹ᵁ U) (z10.KaehlerDifferential.map (fac gY gX φ hφ U)
    (z10.KaehlerDifferential.d b))=_
  rw [z10.KaehlerDifferential.map_d]
  rfl
def k1pre:gY.kaehlerPresheaf⟶((zPF φ).obj xE).val where
  app U:=k1app gY gX φ hφ U.unop
  naturality {U U'} i:=by
    obtain ⟨U⟩:=U; obtain ⟨U'⟩:=U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b))=
      gX.kaehler.val.map ((wM φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK,k1app_dK,k1app_dK,map_unit1,kp_map_dK,φ_naturality_apply]
abbrev adjY:=zSA (𝟙 Y.ringCatSheaf.obj)
def k1:gY.kaehler⟶(zPF φ).obj xE:=((adjY (Y:=Y)).homEquiv gY.kaehlerPresheaf ((zPF φ).obj xE)).symm (k1pre gY gX φ hφ)
ec 1
ec 3 open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange rc
section DifferentialMap
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hφ:φ≫gY=gX≫q11)
def differentialMap:(zPB φ).obj gY.kaehler⟶xE:=((zPA φ).homEquiv _ _).symm (k1 gY gX φ hφ)
theorem differentialMap_isIso(hc:CategoryTheory.IsPullback φ gX gY (q11))[SmoothOfRelativeDimension 1 gY]:IsIso (differentialMap gY gX φ hφ):=by sorry
ec 1 variable {X Y:Scheme.{u}}
def pullbackEqIso{f g:X⟶Y}(h:f=g)(M:wB):(zPB f).obj M≅(zPB g).obj M:=
  eqToIso (by cases h; rfl)
def squarePullbackIso{A B X Y:Scheme.{u}}(a:A⟶B)(s:B⟶Y)(t:A⟶X)(b:X⟶Y)(h:a≫s=t≫b)(M:wB):(zPB a).obj ((zPB s).obj M)≅(zPB t).obj ((zPB b).obj M):=(zPC a s).app M≪≫pullbackEqIso h M≪≫((zPC t b).app M).symm
section PointedComparison
variable {A B:Type u} [z0 A] [z0 B] [z29 A B] {X Y:zS.{u}} (gY:Y⟶Spec (zCR A)) (gX:X⟶Spec (zCR B)) (φ:X⟶Y) (hc:CategoryTheory.IsPullback φ gX gY (q11)) [SmoothOfRelativeDimension 1 gY] (s:Spec (zCR A)⟶Y) (t:Spec (zCR B)⟶X) (hpt:t≫φ=q11≫s)
def pointedDifferentialIso:(zPB (q11)).obj ((zPB s).obj gY.kaehler)≅(zPB t).obj xE:=by
  letI:=differentialMap_isIso gY gX φ hc.w hc
  exact squarePullbackIso _ s t φ hpt.symm gY.kaehler≪≫
    (zPB t).mapIso (asIso (differentialMap gY gX φ hc.w))
ec 1
ec 2 open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange namespace ArithmeticThetaOpenHodgeR0180 rc
abbrev zero{S:Type u}[z0 S](E:EllipticFamily S):Base S⟶wH:=(qJ).val
abbrev hodge{S:Type u}[z0 S](E:EllipticFamily S):=(zPB (zero E)).obj E.projection.kaehler
abbrev power{S:Type u}[z0 S](E:EllipticFamily S)(n:ℕ):=tp (Base S) (hodge E) n
structure Test(S:Type u)[z0 S](E:EllipticFamily S)(R:Type u)[z0 R](W:z3 R)(G:Law R W) where (scalar:S→+*R) (map:Curve R W⟶wH) (cartesian:IsPullback map (qA) vR (baseMap S R scalar)) (origin_eq:origin R W≫map=baseMap S R scalar≫zero E) (nsmul_eq:∀ n,wJ n≫map=map≫wG n)
def comparison{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G):(zPB q52).obj (hodge E)≅Hodge R W:=by
  letI:z29 S R:=C.scalar.toAlgebra
  letI:SmoothOfRelativeDimension 1 vR:=E.smooth
  exact pointedDifferentialIso vR (qA) xH
    C.cartesian (zero E) (qG) C.origin_eq
ec 1 open ArithmeticThetaOpenHodgeR0180
section rc variable (k:Type u) [z1 k] (L:ℕ) (A:la k L)
def ArithmeticThetaCompatibleLevelR0178.Classifies(B:tm k L A)(C:cc k L A B)(Q:cq k L A B C)(R:Type u)[z0 R][z29 k R](W:z3 R)(G:Law R W)(M:q58)(b:Base R⟶Base xD)(f:Curve R W⟶vV):Prop:=b≫vK (zCH (algebraMap k xD))= vK (zCH (algebraMap k R))∧IsPullback f (qA) vZ (qF)∧origin R W≫f=(qF)≫(wR (𝟙 _)).val∧M.x.val≫f=(qF)≫A.marking.x.val∧M.y.val≫f=(qF)≫A.marking.y.val
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
ec 1
section rc variable (k:Type u) [z1 k] [z2 k]
def ArithmeticThetaCubicModelR0144.rootSeries(r:ℕ)(j:Fin 3):z4 k:=if j.val=0 then vT r 0 (-1) else vT r (r/2) (if j.val=1 then 1 else -1) end
open ArithmeticThetaCubicModelR0144 namespace ArithmeticThetaCompactifiedDifferentialR0145 rc variable (k:Type u) [z1 k] [z2 k]
def root(r:ℕ)(j:Fin 3):z5 k:=q2 (rootSeries k r j)
def curve(r:ℕ):z3 (z5 k) where
  a₁:=0
  a₂:=-(root k r 0+root k r 1+root k r 2)
  a₃:=0
  a₄:=root k r 0*root k r 1+root k r 0*root k r 2+root k r 1*root k r 2
  a₆:=-(root k r 0*root k r 1*root k r 2)
abbrev projectiveCurve(r:ℕ):zS.{u}:=projModelCR (curve k r).toProjective
abbrev ChartRing(r:ℕ):=z3.DrinfeldGlobal.ZChartRing (curve k r).toProjective
def chartInclusion(r:ℕ):Spec (zCR (ChartRing k r))⟶projectiveCurve k r:=z3.DrinfeldGlobal.zChartι (curve k r).toProjective
def relativeD{F:Type u}[z0 F]{C:zS.{u}}(f:C⟶Spec (zCR F))(U:C.Opens)(a:C.presheaf.obj (qI)):Γ(f.kaehler,U):=
  letI:z29 F (C.presheaf.obj (qI)):=f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (qI)) a)
ec 1
section rc variable (k:Type u) [z1 k] [z2 k] (r:ℕ)
def ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart.chartScalar:z5 k→+*ChartRing k r:=(z24.fromZeroRingHom (projModelGradingCR (curve k r).toProjective) (Submonoid.powers (coord (curve k r).toProjective 2))).comp (algebraMap (z5 k) (projModelGradingCR (curve k r).toProjective 0)) end
namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential rc
section ChartEquiv
variable {B:Type u} [z0 B] {C:zS.{u}} (i:Spec (zCR B)⟶C) [IsOpenImmersion i]
def chartRingEquiv:Γ(C,i ''ᵁ ⊤) ≃+*B:=((i.appIso ⊤)≪≫zS.ΓSpecIso (zCR B)).commRingCatIsoToRingEquiv
ec 1 variable (k:Type u) [Field k] [CharZero k] (r:ℕ)
local instance zchartAlgebra:z29 (z5 k) (ChartRing k r):=(ProjectiveCubicChart.chartScalar k r).toAlgebra
variable {C:zS.{u}} (E:C≅projectiveCurve k r)
abbrev zLeg:=chartInclusion k r≫E.inv
instance zLeg_open:IsOpenImmersion (zLeg k r E):=by dsimp [zLeg,chartInclusion]; infer_instance
abbrev zOpen:C.Opens:=zLeg k r E ''ᵁ ⊤
abbrev zSection:ChartRing k r ≃+*Γ(C,zOpen k r E):=(chartRingEquiv (zLeg k r E)).symm
ec 2 namespace ArithmeticThetaTateCuspsR0181 rc variable (k:Type u) [z1 k] [z2 k] (L:ℕ)
abbrev TateCurve:=ArithmeticThetaCompactifiedDifferentialR0145.curve k L
abbrev Disk:=Base (z4 k)
abbrev Puncture:=Base (z5 k)
def genericInclusion:Puncture k⟶Disk k:=vK (zCH (q2))
def diskStructure:Disk k⟶Base k:=vK (zCH (algebraMap k (z4 k)))
def closedPoint:Disk k:=⟨IsLocalRing.maximalIdeal (z4 k),inferInstance⟩
structure TateLevel where (elliptic:(qD).IsElliptic) (law:Law (z5 k) (qD)) (originLaw:IsOriginLaw (z5 k) (qD) law) (marking:FullLevel (z5 k) (qD) law L (𝟙 (Puncture k)))
def Extends(D:ld k L)(X:q1)(b:Puncture k⟶OpenBase k L D)(d:Disk k⟶vS):Prop:=d≫X.projection=diskStructure k∧genericInclusion k≫d=b≫wF∧d (closedPoint k)∈boundary k L D X
ec 1 open ArithmeticThetaTateCuspsR0181 namespace ArithmeticThetaBoundaryHodgeR0182 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ)
abbrev CurveFrame:=(z9.unit (q9).ringCatSheaf:(q9).Modules)≅(structureMap (z5 k) (qD)).kaehler
def Normalized(δ:CurveFrame k L):Prop:=
  let E:=Iso.refl (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k L)
  let U:=ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen k L E
  let x:=vU k L E
    (wP (qD).toProjective)
  let y:=vU k L E
    (wO (qD).toProjective)
  vL
    (structureMap (z5 k) (qD)) U x=
      (2*y)•xL δ.hom U (1:Γ(q9,U))
def hodgeGenerator(δ:CurveFrame k L):Γ(q33,⊤):=
  res _ (by simp) (vE
    (origin (z5 k) (qD)) (xL δ.hom ⊤ (1:Γ(q9,⊤))))
structure Test(D:ld k L) where (level:TateLevel k L) (base:Puncture k⟶OpenBase k L D) (map:q9⟶vW) (classifies:ArithmeticThetaCompatibleLevelR0178.Classifies k L wU D.two D.cover D.quotient (z5 k) (qD) level.law level.marking base map) (nsmul_eq:∀ n,level.law.schemeNsmul n≫map=map≫D.atlas.descent.family.law.schemeNsmul n) (differential:CurveFrame k L) (normalized:Normalized k L differential)
structure DiskTest(D:ld k L)(X:q1) extends Test k L D where (disk:Disk k⟶vS) (extends_eq:Extends k L D X base disk)
abbrev openHodge(D:ld k L):=(zPB vJ).obj q47
abbrev openPower(D:ld k L)(n:ℕ):=tp (OpenBase k L D) (openHodge k L D) n
def testIso{D:ld k L}(T:Test k L D):(zPB (T.base≫vJ)).obj q47≅q33:=by
  let ι:vC→+*z5 k:=
    (Spec.preimage (T.base≫vJ)).hom
  have hmap:baseMap vC (z5 k) ι=
      T.base≫vJ:=Spec.map_preimage _
  let C:xK vC
      vO (z5 k) (qD) T.level.law:=
    { scalar:=ι
      map:=T.map
      cartesian:=by rw [hmap]; exact T.classifies.2.1
      origin_eq:=by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq:=T.nsmul_eq }
  exact pullbackEqIso hmap.symm q47≪≫comparison C
def openTestIso{D:ld k L}(T:Test k L D):(zPB T.base).obj (openHodge k L D)≅q33:=(zPC T.base vJ).app _≪≫testIso k L T
structure Extension(D:ld k L)(X:q1) where (line:X.space.Modules) (invertible:wT line) (onOpen:(zPB wF).obj line≅openHodge k L D)
def diskGenericIso{D:ld k L}{X:q1}(H:Extension k L D X)(T:DiskTest k L D X):(zPB (genericInclusion k)).obj (q50)≅q33:=(zPC (genericInclusion k) T.disk).app vM≪≫pullbackEqIso T.extends_eq.2.1 vM≪≫ ((zPC T.base wF).app vM).symm≪≫(zPB T.base).mapIso H.onOpen≪≫openTestIso k L T.toTest
def ExtendsGenerator{D:ld k L}{X:q1}(H:Extension k L D X)(T:DiskTest k L D X)(η:Γ(q50,⊤)):Prop:=
  IsFrame (q50) ⊤ η∧
  res _ (by simp) ((diskGenericIso k L H T).hom.app _
    (vE (genericInclusion k) η))=
      hodgeGenerator k L T.differential
def Canonical{D:ld k L}{X:q1}(H:Extension k L D X):Prop:=∀ T:DiskTest k L D X,∃! η:Γ(q50,⊤),ExtendsGenerator k L H T η
ec 1 open ArithmeticThetaBoundaryHodgeR0182 open ArithmeticThetaBoundaryHodgeR0182 renaming Extension → ex, Canonical → ca namespace ArithmeticThetaSheafTensor rc variable (X:zS.{u})
ec 1
section rc
def ArithmeticThetaTensorPower.tensorPowerSection(X:zS.{u})(H:vB):(n:ℕ)→ (U:vH)→ Γ(H,U)→ Γ(tp X H n,U) | 0,U,_=> (1:Γ(X,U)) | n+1,U,s=> tensorSection X (tp X H n) H U (tensorPowerSection X H n U s) s
end
namespace P458 rc
def pullSection{X Y:Scheme.{u}}(f:X⟶Y){H:wB}{U:xC}(s:Γ(H,U)):Γ((zPB f).obj H,f ⁻¹ᵁ U):=((zPA f).unit.app H).app U s
def Compatible{X Y:Scheme.{u}}(f:X⟶Y)(H K:wB)(M N:vB)(e:(zPB f).obj H≅M)(d:(zPB f).obj K≅N)(q:(zPB f).obj (sheafTensor Y H K)≅sheafTensor X M N):Prop:= ∀ (U:xC) (s:Γ(H,U)) (t:Γ(K,U)),q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t))=tensorSection X M N (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor{X Y:Scheme.{u}}(f:X⟶Y)(H K:wB)(M N:vB)(e:(zPB f).obj H≅M)(d:(zPB f).obj K≅N):∃! q:(zPB f).obj (sheafTensor Y H K)≅sheafTensor X M N,Compatible f H K M N e d q:=by sorry
ec 1
section rc
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
def ArithmeticThetaPullback.pullback_unit_iso(X Y:zS.{u})(p:X⟶Y):(zPB p).obj (z9.unit Y.ringCatSheaf)≅q24:=by
  letI:(wM p.base).Final:=by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤,by simp⟩
  let e:=asIso (z9.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
end
open ArithmeticThetaPullback
section rc
def P505.binary{X Y:Scheme.{u}}(f:X⟶Y)(H K:wB):(zPB f).obj (sheafTensor Y H K)≅sheafTensor X ((zPB f).obj H) ((zPB f).obj K):=Classical.choose (P458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists end
namespace ArithmeticThetaPullback rc
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor(X:zS.{u}):z7 wC:=PresheafOfModulesOfCommRing.monoidalCategory (R:=X.presheaf)
def sheafTensorMap(X:zS.{u}){H H' K K':vB}(f:H⟶H')(g:K⟶K'):sheafTensor X H K⟶sheafTensor X H' K':=(zSF q7).map (f.val ⊗ₘ g.val)
def sheafTensorCongr(X:zS.{u}){H H' K K':vB}(e:H≅H')(d:K≅K'):sheafTensor X H K≅sheafTensor X H' K':=(zSF q7).mapIso (tensorIso ((z9.forget _).mapIso e) ((z9.forget _).mapIso d))
ec 1
section rc
def P505.powerComparison(X Y:zS.{u})(f:X⟶Y)(H:wB):(n:ℕ)→ (zPB f).obj (tp Y H n)≅tp X ((zPB f).obj H) n | 0=> pullback_unit_iso X Y f | n+1=> binary f (tp Y H n) H≪≫sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end
namespace ArithmeticThetaGeometricNormR0150 rc variable {X Y:zS.{u}} [IsIntegral X] [IsIntegral Y]
def IsFieldMap(f:X⟶Y)(φ:xB→+*wE):Prop:=X.fromSpecStalk (genericPoint X)≫f=vK (zCH φ)≫Y.fromSpecStalk (genericPoint Y)
def fieldNorm(φ:xB→+*wE)(g:wE):xB:=
  letI:=φ.toAlgebra
  z29.norm xB g
ec 1 namespace ArithmeticThetaGeneralEllipticKatoR0168 rc variable (F:Type u) [z1 F]
abbrev Curve(W:z3 F):zS.{u}:=projModelCR vD
def structureMap(W:z3 F):Curve F W⟶Spec (zCR F):=projModelStrCR vD
def origin(W:z3 F):Spec (zCR F)⟶Curve F W:=(kwZeroSect F W).val
abbrev Law(W:z3 F):=WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)
def IsOriginLaw(W:z3 F)(G:Law F W):Prop:=(∀ {V:zS.{u}} (t:V⟶Spec (zCR F)),(G.one t).val=t≫origin F W)∧(∀ {V:zS.{u}} (t:V⟶Spec (zCR F)) (x y:sh t (structureMap F W)),G.mul t x y=G.mul t y x)
def originPoint(W:z3 F):Curve F W:=origin F W (@IsLocalRing.closedPoint F _ (@HenselianLocalRing.toIsLocalRing F _ (Field.henselian F)))
def katoOrder(W:z3 F)(G:Law F W)(c:ℕ)(x:Curve F W):ℤ:=by
  classical
  exact (if x=originPoint F W then (c:ℤ)^2 else 0) - (if wJ c x=originPoint F W then 1 else 0)
def HasKatoDivisor(W:z3 F)(G:Law F W)(c:ℕ)[IsIntegral (qN)][IsLocallyNoetherian (qN)](g:(qN).functionField):Prop:=g≠0∧∀ x:Curve F W,zS.ord g x=katoOrder F W G c x
def IsKatoFunction(W:z3 F)(G:Law F W)(c:ℕ)[IsIntegral (qN)][IsLocallyNoetherian (qN)](g:(qN).functionField):Prop:=HasKatoDivisor F W G c g∧∀ d:ℕ,0 < d→ Nat.Coprime c d→ ∀ φ:(qN).functionField→+*(qN).functionField,q63→ wV φ g=g
ec 1 namespace ArithmeticThetaRelativeKatoR0169 rc variable (R:Type u) [z0 R] [z15 R]
abbrev GenericCurve(W:z3 R):zS.{u}:=ArithmeticThetaGeneralEllipticKatoR0168.Curve (z22 R) (W.map q8)
structure GenericComparison(W:z3 R)(G:Law R W)[q37][q49] where (law:ArithmeticThetaGeneralEllipticKatoR0168.Law (z22 R) (W.map q8)) (originLaw:ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (z22 R) (W.map q8) law) (map:GenericCurve R W⟶Curve R W) (cartesian:IsPullback map (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (z22 R) (W.map q8)) (qA) (vK (zCH q8))) (origin_eq:ArithmeticThetaGeneralEllipticKatoR0168.origin (z22 R) (W.map q8)≫map=vK (zCH q8)≫origin R W) (multiplication_eq:∀ n:ℕ,law.schemeNsmul n≫map=map≫wJ n) (field:(qC).functionField ≃+*(GenericCurve R W).functionField) (field_eq:wS map field.toRingHom)
def katoOrder(W:z3 R)(G:Law R W)(c:ℕ)(x:Curve R W):ℤ:=by
  classical
  exact (if x∈wK (qG) then (c:ℤ)^2 else 0) - (if wJ c x∈wK (qG) then 1 else 0)
variable (W:z3 R) (G:Law R W) variable [q37] [q40]
def IsRelativeKato(c:ℕ)(g:(qC).functionField):Prop:=g≠0∧(∀ x:Curve R W,Order.coheight x=1→ zS.ord g x=katoOrder R W G c x)∧(∀ d:ℕ,0 < d→ Nat.Coprime c d→ ∀ φ:(qC).functionField→+*(qC).functionField,q63→ wV φ g=g)
ec 1 namespace ArithmeticThetaRelativeKatoNaturalityR0170 rc variable (R:Type u) [z0 R] [z15 R] variable (W:z3 R) (G:Law R W)
def identityIdeal:(qC).IdealSheafData:=(qG).ker
def torsionIdeal(n:ℕ):(qC).IdealSheafData:=(identityIdeal R W).comap (wJ n)
variable [q37] [q40] variable [q49] [q55]
def Normalized(c:ℕ)(g:(qC).functionField):Prop:=IsRelativeKato R W G c g∧∀ C:GenericComparison R W G,ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (z22 R) (W.map q8) C.law c (C.field g)
def HasValue(P:Spec (zCR R)⟶Curve R W)(g:(qC).functionField)(v:R):Prop:=∃ (U:(qC).Opens) (hU:z30 U) (e:(⊤:(Spec (zCR R)).Opens)≤P ⁻¹ᵁ U) (a:q51),z25 a∧@zS.germToFunctionField (qC) _ U hU a=g∧(zS.ΓSpecIso (zCR R)).hom (P.appLE U ⊤ e a)=v
ec 1 open ArithmeticThetaRelativeKatoNaturalityR0170 namespace ArithmeticThetaRelativeDiscriminantR0171 rc
def localDifferential(R:Type u)[z0 R](W:z3 R)(U:(qC).Opens)(a:q51):Γ(Hodge R W,(qG) ⁻¹ᵁ U):=vE (qG) (vL (qA) U a)
def localPower(R:Type u)[z0 R](W:z3 R)(n:ℕ)(U:(qC).Opens)(a:q51):Γ(HodgePower R W n,(qG) ⁻¹ᵁ U):=tensorPowerSection (Base R) (Hodge R W) n ((qG) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R:Type u) [z0 R] [z15 R] variable (W:z3 R) (G:Law R W)
def IdentityChart(c:ℕ)(U:(qC).affineOpens)(a:q48):Prop:=IsRegular a∧(identityIdeal R W).ideal U=xP ({a}:Set _)∧(torsionIdeal R W G c).ideal U=(identityIdeal R W).ideal U
variable [q37]
def RepresentsInitial(c:ℕ)(g:(qC).functionField)(d:Γ(HodgePower R W (c^2-1),⊤)):Prop:=∀ (U:(qC).affineOpens) [z30 U.1] (a:q48),IdentityChart R W G c U a→ ∃ ε:(q48)ˣ,(c:(qC).functionField)*g=(qC).germToFunctionField U.1 ((ε:_)*a^(c^2-1))∧ res (HodgePower R W (c^2-1)) le_top d=(qG).app U.1 (ε:_)•localPower R W (c^2-1) U.1 a
ec 1
section rc
def ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.powerCongr(X:zS.{u}){H K:vB}(e:H≅K):(n:ℕ)→ tp X H n≅tp X K n | 0=> Iso.refl _ | n+1=> sheafTensorCongr X (powerCongr X e n) e
end
section rc
def ArithmeticThetaPullback.pullbackGlobalSection{X Y:Scheme.{u}}(p:X⟶Y)(M:wB):Γ(M,⊤)→ Γ((zPB p).obj M,p ⁻¹ᵁ (⊤:xC)):=fun s=> ((zPA p).unit.app M).app ⊤ s end
section rc
def P509.HodgeBaseChange.tensorComparison{X Y:Scheme.{u}}(p:X⟶Y)(H:wB)(K:vB)(e:(zPB p).obj H≅K)(n:ℕ):(zPB p).obj (tp Y H n)≅tp X K n:=P505.powerComparison X Y p H n≪≫powerCongr X e n end
namespace P509.OpenHodge rc
def powerComparison{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G)(n:ℕ):(zPB q52).obj (power E n)≅HodgePower R W n:=P509.HodgeBaseChange.tensorComparison q52 (hodge E) (Hodge R W) (comparison C) n
def pullSection{S R:Type u}[z0 S][z0 R]{E:EllipticFamily S}{W:z3 R}{G:Law R W}(C:Test S E R W G)(n:ℕ)(s:Γ(power E n,⊤)):Γ(HodgePower R W n,⊤):=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (vE q52 s))
def IsD2{S:Type u}[z0 S](E:EllipticFamily S)(d:Γ(power E 24,⊤)):Prop:=IsFrame (power E 24) ⊤ d∧∀ (R:Type u) [z0 R] [z15 R] [z17 R] [z16 R] [z29 ℚ R] (W:z3 R) [W.IsElliptic] [q37] [q40] [q49] [q55] (G:Law R W),IsOriginLaw R W G→ ∀ (C:Test S E R W G) (g:(qC).functionField),Normalized R W G 5 g→ RepresentsInitial R W G 5 g (pullSection C 24 d)
ec 2 namespace P509.BoundaryHodge rc variable (k:Type) [z1 k] [z2 k] (L:ℕ)
def pullToOpen{D:ld k L}(n:ℕ)(s:Γ(power vO n,⊤)):Γ(openPower k L D n,⊤):=
  res _ (by simp) ((P505.powerComparison _ _
    vJ q47 n).hom.app _
      (vE vJ s))
def restrictPower{D:ld k L}{X:q1}(H:ex k L D X)(n:ℕ)(s:Γ(tp vS vM n,⊤)):Γ(openPower k L D n,⊤):=
  res _ (by simp) ((P509.HodgeBaseChange.tensorComparison wF vM (openHodge k L D)
    H.onOpen n).hom.app _ (vE wF s))
ec 2
section rc variable (R:Type u) [z0 R] (W:z3 R) (G:Law R W)
def ArithmeticThetaFullLevelCoverR0175.coordinatePoint{L:ℕ}(A:q58)(i j:Fin L):Base R⟶Curve R W:=(G.mul (𝟙 (Base R)) (wL (𝟙 (Base R)) xN A.x) (wL (𝟙 (Base R)) j.val A.y)).val end
namespace ArithmeticThetaOpenHodgeR0180 rc
theorem IsD2._proof_1.{u_1}:∀ (R : Type u_1) [inst : CommRing R] (W : WeierstrassCurve R)   [AlgebraicGeometry.IsIntegral (xF R W)],   IrreducibleSpace ↥(xF R W):=by sorry
sc [`ArithmeticThetaOpenHodgeR0180.IsD2._proof_1]
def IsKatoValue{S:Type u}[z0 S](E:EllipticFamily S)(c:ℕ)(P:Base S⟶wH)(v:S):Prop:=z25 v∧∀ (R:Type u) [z0 R] [z15 R] [z17 R] [z16 R] [z29 ℚ R] (W:z3 R) [W.IsElliptic] [q37] [q40] [q49] [q55] (G:Law R W),IsOriginLaw R W G→ ∀ (C:Test S E R W G) (P':Base R⟶Curve R W),P'≫structureMap R W=𝟙 _→ P'≫xH=baseMap S R C.scalar≫P→ ∀ g:(qC).functionField,Normalized R W G c g→ HasValue R W P' g (C.scalar v)
structure Pointed(S:Type u)[z0 S](E F:EllipticFamily S) where (map:wH⟶xJ) (over_eq:map≫F.projection=vR) (zero_eq:zero E≫map=zero F)
def imagePoint{S:Type u}[z0 S]{E F:EllipticFamily S}(f:Pointed S E F){T:zS.{u}}(t:T⟶Base S)(P:sh t vR):sh t F.projection:=
  ⟨P.val≫f.map,by rw [Category.assoc,f.over_eq,P.property]⟩
def IsHom{S:Type u}[z0 S]{E F:EllipticFamily S}(f:Pointed S E F):Prop:=∀ (T:zS.{u}) (t:T⟶Base S) (P Q:sh t vR),imagePoint f t (E.law.mul t P Q)=F.law.mul t (imagePoint f t P) (imagePoint f t Q)
def familyHodgeMap{S:Type u}[z0 S]{E F:EllipticFamily S}(f:Pointed S E F):hodge F⟶hodge E:=
  (pullbackEqIso f.zero_eq.symm F.projection.kaehler).hom≫
    ((zPC (zero E) f.map).app F.projection.kaehler).inv≫
    (zPB (zero E)).map
      (differentialMap F.projection vR f.map (by simpa using f.over_eq))
structure Quotient(S:Type u)[z0 S](E:EllipticFamily S)(m:ℕ)(P:Base S⟶wH) where (target:EllipticFamily S) (arrow:Pointed S E target) (hom:IsHom arrow) (finite:IsFinite arrow.map) (etale:Etale arrow.map) (surjective:Surjective arrow.map) (degree:∀ z,arrow.map.finrank z=m) (kernel:(zero target).ker.comap arrow.map=⨅ i:Fin m,(P≫wG xN).ker) (universal:∀ (F:EllipticFamily S) (f:Pointed S E F),IsHom f→ (∀ i:Fin m,P≫wG xN≫f.map=zero F)→ ∃! g:Pointed S target F,IsHom g∧arrow.map≫g.map=f.map)
variable (k:Type u) [z1 k] (L:ℕ) (A:la k L)
abbrev levelFamily:=A.descent.family
def kernelPoint(m:ℕ):Base vI⟶(qE).curve:=((qE).law.nsmul (𝟙 _) (L/m) A.marking.x).val
def liftPoint(m N a b:ℕ):Base vI⟶(qE).curve:=((qE).law.mul (𝟙 _) ((qE).law.nsmul (𝟙 _) (L/(m*N)*b) A.marking.x) ((qE).law.nsmul (𝟙 _) (L/N*a) A.marking.y)).val
def scalar(S:Type u)[z0 S](v:S):(Base S).presheaf.obj (xI ⊤):=(zS.ΓSpecIso (zCR S)).inv v
def IsNormalizedPower(m N:ℕ)(Q:Quotient vI (qE) m (kernelPoint k L A m))(d:Γ(power Q.target 24,⊤))(v:vI)(F:Γ(power (qE) (((1+12*N)^2-1)/2),⊤)):Prop:=∀ (U:(q54).Opens) (η:Γ(hodge Q.target,U)) (a:(q54).presheaf.obj (qI)),IsFrame (hodge Q.target) U η→ res (power Q.target 24) le_top d=a•tensorPowerSection q54 (hodge Q.target) 24 U η→ res (power (qE) (((1+12*N)^2-1)/2)) le_top F=((q54).presheaf.map (homOfLE (show U≤⊤ from le_top)).op (scalar vI ((algebraMap k vI (m:k)⁻¹)^(((1+12*N)^2-1)/2)*v))*a^(((1+12*N)^2-1)/48))• tensorPowerSection q54 (hodge (qE)) (((1+12*N)^2-1)/2) U ((familyHodgeMap Q.arrow).app U η)
ec 1
section rc variable (k:Type u) [z1 k] [z2 k] (L:ℕ)
def ArithmeticThetaTateCuspsR0181.CanonicalMarking(ζ:k)(E:TateLevel k L):Prop:=∀ i j:Fin L,xN≠0∨j.val≠0→ HasCoordinates (z5 k) (qD) (coordinatePoint (z5 k) (qD) E.law E.marking i j) (q2 (vT L j.val (ζ ^ xN))) (q2 (xQ L j.val (ζ ^ xN)))
end
namespace ArithmeticThetaUnaryProduct rc
noncomputable def clearedUnaryTheta(m:ℕ)(ν:ℤ):z4 ℤ:=z4.mk (fun n=> ∑ k∈Finset.Icc (-(n:ℤ)) ((n:ℤ)+1),if 12*((m:ℤ)*k+ν)^2=(n:ℤ) then (1:ℤ) else 0)
ec 1 namespace ArithmeticThetaUnaryKatoPowerR0160 rc
def integerSeries(k:Type)[z1 k]:z4 ℤ→+*z5 k:=(HahnSeries.ofPowerSeries ℤ k).comp (z4.map (Int.castRingHom k))
def unary(k:Type)[z1 k](d m:ℕ)(ν:ℤ):z5 k:=integerSeries k (z4.subst (z4.X^d) (wQ m ν))
ec 1
section rc
def ArithmeticThetaBoundaryHodgeR0182.unaryResidue(m N:ℕ)(ν:ℤ):ℕ:=Int.toNat ((((N/2:ℕ):ℤ)+((N/m:ℕ):ℤ)*ν) % (N:ℤ)) end
namespace ArithmeticThetaCompactUnaryR0183 rc
abbrev level(N:ℕ):ℕ:=24*N^2
abbrev exponent(N:ℕ):ℕ:=(1+12*N)^2-1
abbrev weight(N:ℕ):ℕ:=exponent N/2
ec 1 open ArithmeticThetaCompactUnaryR0183
section rc variable (k:Type) [z1 k] [z2 k] (L:ℕ)
def P514.BoundaryHodge.diskPower{D:ld k L}{X:q1}(H:ex k L D X)(T:DiskTest k L D X)(n:ℕ)(s:Γ(tp vS vM n,⊤)):Γ(tp (Disk k) (q50) n,⊤):=
  res _ (by simp) ((P505.powerComparison _ _
    T.disk vM n).hom.app _ (vE T.disk s))
end
namespace P514 rc variable (k:Type) [z1 k] [z2 k] (m N:ℕ)
structure OpenPower(D:q27)(a b:Fin N) where (quotient:Quotient vC (levelFamily k (level N) wU) m (kernelPoint k (level N) wU m)) (discriminant:Γ(power wD 24,⊤)) (intrinsic:P509.OpenHodge.IsD2 wD discriminant) (value:vC) (value_spec:IsKatoValue wD (1+12*N) (liftPoint k (level N) wU m N a.val b.val≫quotient.arrow.map) value) (section_:Γ(power vO (weight N),⊤)) (normalized:IsNormalizedPower k (level N) wU m N quotient discriminant value section_)
def DiskCoefficient{D:q27}{X:q12}(H:q23)(V:q25)(s:Γ(q56,⊤))(f:z4 k):Prop:=∀ η:Γ(q29,⊤),ExtendsGenerator k (level N) H V η→ BoundaryHodge.diskPower k (level N) H V (weight N) s= scalar (z4 k) f•tensorPowerSection (Disk k) (q29) (weight N) ⊤ η
def RealizesUnary{D:q27}{X:q12}(H:q23)(ν:ℤ){a b:Fin N}(A:OpenPower k m N D a b)(s:Γ(q56,⊤)):Prop:=P509.BoundaryHodge.restrictPower k (level N) H (weight N) s=P509.BoundaryHodge.pullToOpen k (level N) (weight N) A.section_∧ IsFrame (power vO (weight N)) ⊤ A.section_∧(∀ V:q25,∃ f:z4 k,f≠0∧DiskCoefficient k N H V s f)∧(∀ (V:q25) (ζ:k),IsPrimitiveRoot ζ (level N)→ CanonicalMarking k (level N) ζ V.level→ ∃ f:z4 k,q2 f=ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N∧DiskCoefficient k N H V s f)
ec 1 namespace P365 rc
abbrev Base(R:Type u)[z0 R]:=Spec (zCR R)
def idealModule{X:Scheme.{u}}(I:wW):vB:=kernel q53
def idealInclusion{X:Scheme.{u}}(I:wW):idealModule I⟶q24:=kernel.ι q53
def pullSection{X Y:Scheme.{u}}(f:X⟶Y){M:wB}{U:xC}(s:Γ(M,U)):Γ((zPB f).obj M,f ⁻¹ᵁ U):=((zPA f).unit.app M).app U s
section Differentials
variable {R:Type u} [z0 R] {X:zS.{u}} (f:X⟶Base R)
def constToPresheaf:(Functor.const (vH)ᵒᵖ).obj (zCR R)⟶X.presheaf where
  app U:=(zS.ΓSpecIso (zCR R)).inv≫f.appLE ⊤ U.unop le_top
  naturality U V i:=by
    simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.id_comp,Category.assoc]
    rw [zS.Hom.appLE_map]
@[reducible] def sectionsAlgebra(U:vH):z29 R Γ(X,U):=((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf:wC:=PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
def kaehler:vB:=(zSF q7).obj (kaehlerPresheaf f)
def kaehlerToSections(U:vH):((kaehlerPresheaf f).obj (op U):Type u)→ (Γ(kaehler f,U):Type u):=fun s=> (((zSA q7).unit.app (kaehlerPresheaf f)).app (op U)).hom s
def relativeD(U:vH)(a:Γ(X,U)):Γ(kaehler f,U):=
  letI:z29 R Γ(X,U):=sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X,U) a)
ec 1
ec 1 open P365 namespace P436 rc variable {R:Type u} [z0 R] {X S:zS.{u}} (c:X⟶Spec (zCR R)) (e:S⟶X)
def Normalized(m:(zPB e).obj (idealModule e.ker)⟶(zPB e).obj (kaehler c)):Prop:=∀ (U:vH) (x:Γ(idealModule e.ker,U)),m.app (e ⁻¹ᵁ U) (pullSection e x)=pullSection e (relativeD c U ((idealInclusion e.ker).app U x))
theorem canonicalConormalMap:∃! m:(zPB e).obj (idealModule e.ker)⟶(zPB e).obj (kaehler c),Normalized c e m:=by sorry
def conormalMap:(zPB e).obj (idealModule e.ker)⟶(zPB e).obj (kaehler c):=(canonicalConormalMap c e).exists.choose
ec 1 namespace P544 variable {X Y:Scheme.{u}}
abbrev unitMap(f:X⟶Y):z9.unit Y.ringCatSheaf⟶(z9.pushforward f.toRingCatSheafHom).obj (q24):=z9.unitToPushforwardObjUnit f.toRingCatSheafHom
def idealModule(I:wW):vB:=(kernel (unitMap I.subschemeι):z9 X.ringCatSheaf)
def idealInclusion(I:wW):idealModule I⟶q24:=kernel.ι (unitMap I.subschemeι)
ec 1
namespace ArithmeticThetaLocalWeierstrassR0203 rc
abbrev Base(R:Type u)[z0 R]:=Spec (zCR R)
structure SchemeLaw{S X:Scheme.{u}}(p:X⟶S) where (mul:∀ {T:zS.{u}} (t:T⟶S),sh t p→ sh t p→ sh t p) (one:∀ {T:zS.{u}} (t:T⟶S),sh t p) (inv:∀ {T:zS.{u}} (t:T⟶S),sh t p→ sh t p) (mul_assoc:∀ {T:zS.{u}} (t:T⟶S) (x y z:sh t p),mul t (mul t x y) z=mul t x (mul t y z)) (one_mul:∀ {T:zS.{u}} (t:T⟶S) (x:sh t p),mul t (one t) x=x) (mul_one:∀ {T:zS.{u}} (t:T⟶S) (x:sh t p),mul t x (one t)=x) (inv_mul_cancel:∀ {T:zS.{u}} (t:T⟶S) (x:sh t p),mul t (inv t x) x=one t) (mul_comm:∀ {T:zS.{u}} (t:T⟶S) (x y:sh t p),mul t x y=mul t y x) (mul_natural:∀ {T T':zS.{u}} (t:T⟶S) (t':T'⟶S) (ψ:T'⟶T) (hψ:ψ≫t=t') (x y:sh t p),vY ψ hψ (mul t x y)=mul t' (vY ψ hψ x) (vY ψ hψ y))
structure Family(S:zS.{u}) where (curve:zS.{u}) (p:curve⟶S) (law:SchemeLaw p) (proper:IsProper p) (dimension:SmoothOfRelativeDimension 1 p) (connected:GeometricallyConnected p)
def Family.zero{S:Scheme.{u}}(E:Family S):S⟶wH:=(E.law.one (𝟙 S)).val
ec 1 open ArithmeticThetaLocalWeierstrassR0203 namespace ArithmeticThetaSchemeLevelR0204 rc
def multiple{S:Scheme.{u}}(E:Family S){T:zS.{u}}(t:T⟶S):ℕ→ sh t E.p→ sh t E.p | 0,_=> E.law.one t | n+1,x=> E.law.mul t (multiple E t n x) x
structure FullLevel{S:Scheme.{u}}(E:Family S)(L:ℕ) where (x:sh (𝟙 S) E.p) (y:sh (𝟙 S) E.p) (killed_x:multiple E (𝟙 S) L x=E.law.one (𝟙 S)) (killed_y:multiple E (𝟙 S) L y=E.law.one (𝟙 S)) (avoids:∀ i j:Fin L,xN≠0∨j.val≠0→ Disjoint (wK (E.law.mul (𝟙 S) (multiple E (𝟙 S) xN x) (multiple E (𝟙 S) j.val y)).val) (wK E.zero))
variable (k:Type u) [z1 k] [z2 k] (L:ℕ) (A:la k L)
def UniversalMultiplicative{S:Scheme.{u}}(E:Family S)(b:S⟶vA vI)(f:wH⟶vV):Prop:=∀ (T:zS.{u}) (t:T⟶S) (x y:sh t E.p) (x' y':sh (t≫b) vZ),x'.val=x.val≫f→ y'.val=y.val≫f→ (A.descent.family.law.mul _ x' y').val=(E.law.mul t x y).val≫f
def Classifies(B:tm k L A)(C:cc k L A B)(Q:cq k L A B C){S:zS.{u}}(σ:S⟶q45)(E:Family S)(M:FullLevel E L)(b:S⟶q31)(f:wH⟶vV):Prop:= b≫vK (zCH (algebraMap k xD))=σ∧IsPullback f E.p vZ (qF)∧E.zero≫f=(qF)≫(wR (𝟙 _)).val∧M.x.val≫f=(qF)≫A.marking.x.val∧M.y.val≫f=(qF)≫A.marking.y.val∧UniversalMultiplicative k L A E (qF) f
ec 1 open ArithmeticThetaSchemeLevelR0204
section rc
def ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily{k:Type u}[z1 k](L:ℕ)(A:la k L):Family (vA vI) where
  curve:=vV
  p:=vZ
  law:=
    { mul:=A.descent.family.law.mul,one:=wR
      inv:=A.descent.family.law.inv
      mul_assoc:=A.descent.family.law.mul_assoc
      one_mul:=A.descent.family.law.one_mul
      mul_one:=A.descent.family.law.mul_one
      inv_mul_cancel:=A.descent.family.law.inv_mul_cancel
      mul_comm:=A.descent.family.commutative
      mul_natural:=A.descent.family.law.mul_natural }
  proper:=A.descent.family.proper
  dimension:=A.descent.family.smooth
  connected:=A.descent.family.connected
end
namespace P519.Hodge rc
abbrev Cotangent{S:Scheme.{u}}(E:Family S):S.Modules:=(zPB E.zero).obj q35
def IdealCompatible{S T:Scheme.{u}}(E:Family S)(F:Family T)(f:xJ⟶wH)(i:(zPB f).obj q35≅(wY F.zero.ker)):Prop:=i.hom≫(P544.idealInclusion F.zero.ker)=(zPB f).map (P544.idealInclusion E.zero.ker)≫(pullback_unit_iso xJ wH f).hom
def cotangentComparison{S T:Scheme.{u}}(E:Family S)(F:Family T)(b:T⟶S)(f:xJ⟶wH)(hz:F.zero≫f=b≫E.zero)(i:(zPB f).obj q35≅(wY F.zero.ker)):(zPB b).obj (Cotangent E)≅Cotangent F:=squarePullbackIso b E.zero F.zero f hz.symm q35≪≫(zPB F.zero).mapIso i
abbrev affineDifferential{R:Type u}[z0 R](E:Family (vA R)):Cotangent E⟶(zPB E.zero).obj E.p.kaehler:=P436.conormalMap E.p E.zero
variable (k:Type u) [z1 k] [z2 k] (L:ℕ) (A:la k L) (B:tm k L A) (C:cc k L A B) (Q:cq k L A B C)
abbrev universalFamily:=GlobalSchemeClassifier.universalFamily L A
abbrev ModularHodge:(q31).Modules:=(zPB Q.inclusion).obj ((zPB (q21).zero).obj (q21).p.kaehler)
def ClassifierHodge{S:Scheme.{u}}(E:Family S)(b:S⟶q31)(f:wH⟶vV)(e:(zPB b).obj (ModularHodge k L A B C Q)≅Cotangent E):Prop:=∃ (hz:E.zero≫f=(qF)≫(q21).zero) (i:(zPB f).obj (wY (q21).zero.ker)≅q35), IdealCompatible q21 E f i∧(zPB b).map ((zPB Q.inclusion).map (affineDifferential q21))≫e.hom=((zPC b Q.inclusion).app (Cotangent q21)).hom≫(cotangentComparison q21 E (qF) f hz i).hom
ec 2 open P519.Hodge namespace P519.Level rc
abbrev constants{k l:Type}[z1 k][z1 l](ι:k→+*l):q44⟶q45:=vK (zCH ι)
abbrev Classifies{k:Type}[z1 k][z2 k]{L:ℕ}(D:ld k L){S:zS.{0}}(σ:S⟶q45)(F:Family S)(M:FullLevel F L)(b:S⟶OpenBase k L D)(f:xJ⟶vW):=ArithmeticThetaSchemeLevelR0204.Classifies k L wU D.two D.cover D.quotient σ F M b f
def RespectsClassifiers{k l:Type}[z1 k][z2 k][z1 l][z2 l]{L:ℕ}(ι:k→+*l)(D:ld k L)(E:ld l L)(f:OpenBase l L E⟶OpenBase k L D):Prop:=f≫openStructure k L D=openStructure l L E≫constants ι∧∀ (S:zS.{0}) (σ:S⟶q44) (F:Family S) (M:FullLevel F L) (b:S⟶OpenBase l L E) (g:xJ⟶E.atlas.descent.family.curve), Classifies E σ F M b g→ ∃ a:xJ⟶vW,Classifies D (σ≫constants ι) F M (b≫f) a
abbrev weight{k:Type}[z1 k][z2 k]{L:ℕ}(D:ld k L):=ModularHodge k L wU D.two D.cover D.quotient
def HodgeCompatible{k l:Type}[z1 k][z2 k][z1 l][z2 l]{L:ℕ}(ι:k→+*l)(D:ld k L)(E:ld l L)(f:OpenBase l L E⟶OpenBase k L D)(e:(zPB f).obj (weight D)≅weight E):Prop:=∀ (S:zS.{0}) (σ:S⟶q44) (F:Family S) (M:FullLevel F L) (b:S⟶OpenBase l L E) (g:xJ⟶E.atlas.descent.family.curve) (a:xJ⟶vW),Classifies E σ F M b g→ Classifies D (σ≫constants ι) F M (b≫f) a→ ∀ (el:(zPB b).obj (weight E)≅Cotangent F) (ek:(zPB (b≫f)).obj (weight D)≅Cotangent F),ClassifierHodge l L E.atlas E.two E.cover E.quotient F b g el→ ClassifierHodge k L wU D.two D.cover D.quotient F (b≫f) a ek→ (zPB b).map e.hom≫el.hom=((zPC b f).app (weight D)).hom≫ek.hom
def Extends{k l:Type}[z1 k][z1 l]{L:ℕ}(ι:k→+*l)(D:ld k L)(E:ld l L)(X:q1)(Y:cp l L E)(f:OpenBase l L E⟶OpenBase k L D)(F:Y.space⟶vS):Prop:=F≫X.projection=Y.projection≫constants ι∧Y.inclusion≫F=f≫wF
ec 2 open P519.Level namespace P519.Boundary rc variable {k l:Type} [z1 k] [z2 k] [z1 l] [z2 l]
def CompactCompatible(ι:k→+*l){L:ℕ}{D:ld k L}{E:ld l L}{X:q1}{Y:cp l L E}(f:OpenBase l L E⟶OpenBase k L D)(F:Y.space⟶vS)(hF:P519.Level.Extends ι D E X Y f F)(e:(zPB f).obj (weight D)≅weight E)(H:ex k L D X)(J:ex l L E Y)(a:(zPB F).obj vM≅J.line):Prop:= (zPB Y.inclusion).map a.hom≫J.onOpen.hom=((zPC Y.inclusion F).app vM).hom≫(pullbackEqIso hF.2 vM).hom≫((zPC f wF).app vM).inv≫(zPB f).map H.onOpen.hom≫e.hom
def GeometricallyCanonical{L:ℕ}{D:ld k L}{X:q1}(H:ex k L D X):Prop:=∀ (l:Type) [z1 l] [z2 l] [z18 l] (ι:k→+*l) (E:ld l L) (Y:cp l L E) (f:OpenBase l L E⟶OpenBase k L D) (F:Y.space⟶vS) (hf:RespectsClassifiers ι D E f) (hF:P519.Level.Extends ι D E X Y f F) (e:(zPB f).obj (weight D)≅weight E),HodgeCompatible ι D E f e→ ∀ J:ex l L E Y,ca l L J→ ∃! a:(zPB F).obj vM≅J.line,CompactCompatible ι f F hF e H J a
ec 2
namespace ArithmeticThetaGlobalFourTorsionR0190 rc variable (R:Type u) [z0 R] (W:z3 R) (G:Law R W) (L:ℕ) (M:vF R W G L (𝟙 (q20)))
def twoLabel(i:Fin 3):q20⟶Curve R W:=![(wL (𝟙 _) (L/2) M.x).val,(wL (𝟙 _) (L/2) M.y).val,(G.mul (𝟙 _) (wL (𝟙 _) (L/2) M.x) (wL (𝟙 _) (L/2) M.y)).val] i
def quarterPoint:q20⟶Curve R W:=(wL (𝟙 _) (L/4) M.y).val
def completedY[z29 ℚ R](x y:R):R:=y+algebraMap ℚ R (1/2)*(W.a₁*x+W.a₃)
def Labels[z29 ℚ R](e:Fin 3→ R):Prop:=∀ i,HasCoordinates R W (twoLabel R W G L M i) (e i) (-(algebraMap ℚ R (1/2))*(W.a₁*e i+W.a₃))
def RootData[z29 ℚ R](e:Fin 3→ R)(x y g:R):Prop:=Labels R W G L M e∧SplitCubic R W e∧HasCoordinates R W (quarterPoint R W G L M) x y∧z25 (completedY R W x y)∧z25 g∧2*completedY R W x y*g=(x-e 0)^2 - (e 0-e 1)*(e 0-e 2)∧g^2=e 1-e 0
abbrev CurveFrame:=(z9.unit (qC).ringCatSheaf:(qC).Modules)≅(qA).kaehler
def differentialSection(δ:CurveFrame R W):Γ((qA).kaehler,⊤):=xL δ.hom ⊤ (1:Γ(Curve R W,⊤))
def NormalizedFrame(δ:CurveFrame R W):Prop:=
  let j:=chartInclusion R W
  let p:=j≫structureMap R W
  let x:=wP vD
  let y:=wO vD
  let toGlobal:=(zS.ΓSpecIso (zCR (ChartRing R W))).inv
  vL p ⊤ (toGlobal x)=
    toGlobal (2*y+chartScalar R W W.a₁*x+chartScalar R W W.a₃)•
      (differentialMap (qA) p j (by simp [p])).app ⊤
        (pullbackGlobalSection j (qA).kaehler (differentialSection R W δ))
def hodgeGenerator(δ:CurveFrame R W):Γ(Hodge R W,⊤):=pullbackGlobalSection (qG) (qA).kaehler (differentialSection R W δ)
def RealizesAlpha[z29 ℚ R](a:Γ(Hodge R W,⊤)):Prop:=∃ (e:Fin 3→ R) (x y g:R) (δ:CurveFrame R W),RootData R W G L M e x y g∧NormalizedFrame R W δ∧a=scalar R (2*g)•hodgeGenerator R W δ
section LevelBase
variable (k:Type) [z1 k] [z2 k] (D:ld k L) variable (X:q1) (H:ex k L D X)
def restrictAlpha(a:Γ(vM,⊤)):Γ(openHodge k L D,⊤):=H.onOpen.hom.app ⊤ (pullbackGlobalSection wF vM a)
def thetaAt(L:ℕ):z4 k:=z4.mk (fun n=> if L/2 ∣ n then z4.coeff (n/(L/2)) (ArithmeticThetaTateSeries.theta k) else 0)
ec 1
ec 1 open ArithmeticThetaGlobalFourTorsionR0190
section rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1)
theorem P485.componentIsOpen(x:vS):IsOpen (irreducibleComponent x):=by sorry end
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1)
theorem compactComponent._proof_1:∀ (k : Type) [inst : Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)   (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : ↥vS), IsOpen (irreducibleComponent x):=by sorry
sc [`ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent._proof_1]
def compactComponent(x:vS):X.space.Opens:=⟨irreducibleComponent x,compactComponent._proof_1 k L D X x⟩
ec 2 namespace ArithmeticThetaComponentDegreeR0184 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1) (x:vS)
abbrev componentOpen:X.space.Opens:=CompactHodgeLatticeExtensionR0182.compactComponent k L D X x
abbrev Component:zS:=(componentOpen k L D X x).toScheme
abbrev inclusion:Component k L D X x⟶vS:=(componentOpen k L D X x).ι
abbrev projection:Component k L D X x⟶Spec (zCR k):=inclusion k L D X x≫X.projection
theorem componentIntegral:IsIntegral q5:=by sorry
attribute [instance] componentIntegral
theorem componentLocallyNoetherian:IsLocallyNoetherian q5:=by sorry
attribute [instance] componentLocallyNoetherian
def cuspSet:Set q5:={y | inclusion k L D X x y∈boundary k L D X}
abbrev hodge(H:ex k L D X):(q5).Modules:=(zPB (inclusion k L D X x)).obj vM
ec 1 open ArithmeticThetaComponentDegreeR0184 namespace ArithmeticThetaLineRoot rc
structure LocalFrame(X:zS.{u})(H:vB)(U:vH) where (equiv (V:vH) (hVU:V≤U):Γ(X,V) ≃ₗ[Γ(X,V)] Γ(H,V)) (naturality (V W:vH) (hWV:W≤V) (hVU:V≤U) (a:Γ(X,V)):H.presheaf.map (homOfLE hWV).op (equiv V hVU a)=equiv W (hWV.trans hVU) (wN (homOfLE hWV).op a))
variable (X:zS.{u}) [IsIntegral X]
structure NormalFrameCover(H:vB)(ι:Type v) where (opens:ι→ vH) (covers:(⊤:vH)≤ iSup opens) (nonempty:∀ i,z30 (opens i)) (affine:∀ i,IsAffineOpen (opens i)) (normal:∀ i,z16 Γ(X,opens i)) (frame:∀ i,LocalFrame X H (opens i))
instance {X:zS.{u}} {H:vB} {ι:Type v} (C:NormalFrameCover X H ι) (i:ι):z30 (C.opens i):=C.nonempty i
ec 1 open ArithmeticThetaLineRoot open ArithmeticThetaLineRoot renaming LocalFrame → lf, NormalFrameCover → nf namespace ArithmeticThetaNormalizedSections rc
def sectionCoordinate(X:zS.{u})(H:vB)(U:vH)(e:lf X H U)(s:Γ(H,⊤)):Γ(X,U):=(e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)
def sectionCoefficient(X:zS.{u})[IsIntegral X](H:vB)(U:vH)[z30 U](e:lf X H U)(s:Γ(H,⊤)):wE:=vQ U (sectionCoordinate X H U e s)
ec 1 open ArithmeticThetaNormalizedSections namespace ArithmeticThetaSectionOrder rc
def localOrder(X:zS.{u})[IsIntegral X][q13](H:vB){ι:Type v}(C:nf X H ι)(s:Γ(H,⊤))(i:ι)(x:X):ℤ:=zS.ord (sectionCoefficient X H (C.opens i) (C.frame i) s) x
def MatchesSectionOrder(X:zS.{u})[IsIntegral X][q13](H:vB){ι:Type v}(C:nf X H ι)(s:Γ(H,⊤))(D:X→₀ ℤ):Prop:=∀ (i:ι) (x:X),x∈C.opens i→ D x=localOrder X H C s i x
ec 1 open ArithmeticThetaSectionOrder
section rc
def ArithmeticThetaNormalizedSections.NormalAffine(X:zS.{u}):Prop:=∀ U:vH,IsAffineOpen U→ ∀ [z30 U],z16 Γ(X,U) end
section rc variable (X:zS.{u}) [IsIntegral X]
theorem ArithmeticThetaLineRoot.germ_restrict(U V:vH)[z30 U][z30 V](hVU:V≤U)(a:Γ(X,U)):vQ V (wN (homOfLE hVU).op a)=vQ U a:=by sorry end
section rc
theorem ArithmeticThetaSectionCompletion.normal_stalk_dvr(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(x:X)(hx:Order.coheight x=1):IsDiscreteValuationRing (X.presheaf.stalk x):=by sorry end
namespace ArithmeticThetaGeometricPrerequisites rc
abbrev RationalSections(X:zS.{u})[IsIntegral X](U:vH):=PLift (z30 U)→ wE
def rationalScalars(X:zS.{u})[IsIntegral X](U:vH):Γ(X,U)→+*RationalSections X U where
  toFun a h:=@zS.germToFunctionField X _ U h.down a
  map_one':=by ext h; exact map_one _
  map_zero':=by ext h; exact map_zero _
  map_add' a b:=by ext h; exact map_add _ a b
  map_mul' a b:=by ext h; exact map_mul _ a b
instance rationalSectionsModule(X:zS.{u})[IsIntegral X](U:vH):Module Γ(X,U) (RationalSections X U):=Module.compHom _ (rationalScalars X U)
def rationalRestrict(X:zS.{u})[IsIntegral X]{U V:vH}(h:V≤U)(f:RationalSections X U):RationalSections X V:=fun hV↦f ⟨⟨⟨(q60).1,h (q60).2⟩⟩⟩
def rationalPresheaf(X:zS.{u})[IsIntegral X]:z8 X.ringCatSheaf.obj where
  obj U:=z12.of Γ(X,U.unop) (RationalSections X U.unop)
  map {U V} h:=by
    rcases U with ⟨U⟩
    rcases V with ⟨V⟩
    refine z12.semilinearMapAddEquiv (wN h).hom _ _ ?_
    exact
      { toFun:=rationalRestrict X h.unop.le
        map_add' _ _:=rfl
        map_smul' a f:=by
          ext hV
          letI:z30 V:=hV.down
          letI:z30 U:=⟨⟨(q60).1,h.unop.le (q60).2⟩⟩
          change vQ U a*_=
            vQ V (wN h a)*_
          have hh:h=(homOfLE h.unop.le).op:=Subsingleton.elim _ _
          rw [hh,germ_restrict X U V h.unop.le]
          rfl }
  map_id U:=by ext f; rfl
  map_comp f g:=by ext a; rfl
def boundedSections(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ)(U:vH):z21 Γ(X,U) (RationalSections X U) where
  carrier:={f | ∀ (h:PLift (z30 U)) (x:X),x∈U→
    f h=0∨-D x≤zS.ord (f h) x}
  zero_mem':=by intro h x hx; exact Or.inl rfl
  add_mem':=by
    intro f g hf hg h x hx
    by_cases hfg:f h+g h=0
    · exact Or.inl hfg
    right
    rcases hf h x hx with hf0 | hf0
    · simpa [hf0] using (hg h x hx).resolve_left (by simpa [hf0] using hfg)
    rcases hg h x hx with hg0 | hg0
    · simpa [hg0] using hf0
    by_cases hco:Order.coheight x=1
    · letI:=ArithmeticThetaSectionCompletion.normal_stalk_dvr X hN x hco
      exact (le_min hf0 hg0).trans (zS.ord_add hfg)
    · simpa [zS.ord_eq_zero_of_coheight_neq_one hco] using hf0
  smul_mem':=by
    intro a f hf h x hx
    letI:z30 U:=h.down
    change vQ U a*f h=0∨_
    by_cases ha:a=0
    · left; simp [ha]
    rcases hf h x hx with hf0 | hf0
    · left; simp [hf0]
    · right
      exact hf0.trans (zS.ord_le_smul hx ha (f h))
def divisorSubpresheaf(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ):(rationalPresheaf X).Submodule where
  obj U:=boundedSections X hN D U.unop
  map f:=by
    intro a ha h x hx
    exact ha ⟨⟨⟨x,f.unop.le hx⟩⟩⟩ x (f.unop.le hx)
abbrev divisorPresheaf(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ):=(divisorSubpresheaf X hN D).toPresheafOfModules
theorem divisorPresheaf_isSheaf(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ):TopCat.Presheaf.IsSheaf (divisorPresheaf X hN D).presheaf:=by sorry
def divisorSheaf(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ):vB where
  val:=divisorPresheaf X hN D
  isSheaf:=divisorPresheaf_isSheaf X hN D
theorem rational_order_one(X:zS.{u})[IsIntegral X][q13](x:X):zS.ord (1:wE) x=0:=by sorry
def divisorCanonicalSection(X:zS.{u})[IsIntegral X][q13](hN:NormalAffine X)(D:X→₀ ℤ)(hD:∀ x,0≤D x):Γ(divisorSheaf X hN D,⊤):=
  ⟨fun _↦1,by
    intro h x hx
    right
    simpa [rational_order_one] using neg_nonpos.mpr (hD x)⟩
ec 1 namespace ArithmeticThetaCommonHalfHodgeR0185 rc
structure DivisorLine(Z:zS) where (line:Z.Modules) (section_:Γ(line,⊤))
variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1) (x:vS)
def diskHodgeIso(H:ex k L D X)(V:DiskTest k L D X)(f:Disk k⟶Component k L D X x)(hf:f≫inclusion k L D X x=V.disk):(zPB f).obj (qK)≅q29:=(zPC f (inclusion k L D X x)).app vM≪≫(zS.Modules.pullbackCongr hf).app vM
ec 1 open ArithmeticThetaCommonHalfHodgeR0185 namespace ArithmeticThetaSquareLinesR0192 rc variable (k:Type) [z1 k] [z2 k] (L:ℕ) (D:ld k L) (X:q1) (H:ex k L D X)
def componentAlpha(x:vS)(a:Γ(vM,⊤)):Γ(hodge k L D X x H,⊤):=pullbackGlobalSection (inclusion k L D X x) vM a
def canonicalDivisorData(x:vS)(E:Component k L D X x→₀ ℤ)(hE:∀ y,0≤E y)(hN:NormalAffine q5):DivisorLine q5:=⟨ArithmeticThetaGeometricPrerequisites.divisorSheaf _ hN E,ArithmeticThetaGeometricPrerequisites.divisorCanonicalSection _ hN E hE⟩
ec 1 open ArithmeticThetaSquareLinesR0192 namespace ArithmeticThetaIsogenyHalfLinesR0193 rc
def IsFamilyAlpha(S:Type)[z0 S](E:EllipticFamily S)(M:FamilyLevel S E 4)(a:Γ(hodge E,⊤)):Prop:=IsFrame (hodge E) ⊤ a∧∀ (R:Type) [z0 R] [z15 R] [z17 R] [z16 R] [z29 ℚ R] (W:z3 R) [W.IsElliptic] (G:Law R W),IsOriginLaw R W G→ ∀ (C:xK S E R W G) (B:vF R W G 4 (𝟙 (q20))),B.x.val≫xH=baseMap S R C.scalar≫M.x.val→ B.y.val≫xH=baseMap S R C.scalar≫M.y.val→ RealizesAlpha R W G 4 B ((comparison C).hom.app ⊤ (pullbackGlobalSection q52 (hodge E) a))
variable (k:Type) [z1 k] [z2 k] (L m:ℕ) (D:ld k L)
abbrev SourceFamily:=vO
abbrev CyclicQuotient:=Quotient vC (SourceFamily k L D) m (kernelPoint k L wU m)
def TargetMarking(Q:CyclicQuotient k L m D)(M:FamilyLevel vC Q.target 4):Prop:=M.x.val=liftPoint k L wU m 4 0 1≫Q.arrow.map∧M.y.val=liftPoint k L wU m 4 1 0≫Q.arrow.map
structure OpenAlpha where (quotient:CyclicQuotient k L m D) (marking:FamilyLevel vC wD 4) (marked:TargetMarking k L m D quotient marking) (alpha:Γ(hodge wD,⊤)) (intrinsic:IsFamilyAlpha vC wD marking alpha)
def ambientAlpha(A:OpenAlpha k L m D):Γ(hodge (SourceFamily k L D),⊤):=scalar vC (algebraMap k vC (m:k)⁻¹)•(familyHodgeMap A.quotient.arrow).app ⊤ A.alpha
def openAlpha(A:OpenAlpha k L m D):Γ(openHodge k L D,⊤):=pullbackGlobalSection vJ (hodge (SourceFamily k L D)) (ambientAlpha k L m D A)
def testKernel(V:xG k L D):Puncture k⟶q9:=(V.level.law.nsmul (𝟙 _) (L/m) V.level.marking.x).val
def KernelCoordinates(V:xG k L D)(i:Fin L)(z:kˣ):Prop:=(xN≠0∨(z:k)≠1)∧HasCoordinates (z5 k) (qD) (testKernel k L m D V) (q2 (vT L xN z)) (q2 (xQ L xN z))
def AllowedOrder(i:Fin L)(j:ℕ):Prop:=
  let d:=L/Nat.gcd L xN
  let e:=m/d
  0 < d∧d ∣ m∧0 < e∧e*d=m∧Even j∧
    (j=0∨4*m*j=L*e^2)
variable (X:q1) (H:ex k L D X)
def CompactRealizes(A:OpenAlpha k L m D)(a:Γ(vM,⊤)):Prop:=restrictAlpha L k D X H a=openAlpha k L m D A∧(∀ V:DiskTest k L D X,∀ η:Γ(q29,⊤),ExtendsGenerator k L H V η→ ∃ (i:Fin L) (z:kˣ) (j:ℕ) (v:(z4 k)ˣ),KernelCoordinates k L m D V.toTest i z∧AllowedOrder L m i j∧ pullbackGlobalSection V.disk vM a=scalar (z4 k) (z4.X^j*(v:z4 k))•η)∧(∀ (V:DiskTest k L D X) (ζ:k),IsPrimitiveRoot ζ L→ CanonicalMarking k L ζ V.level→ ∀ η:Γ(q29,⊤),ExtendsGenerator k L H V η→ pullbackGlobalSection V.disk vM a= scalar (z4 k) (thetaAt k (L*m)^2)•η)
def HalfDivisor(x:vS)(a:Γ(vM,⊤))(E:Component k L D X x→₀ ℤ):Prop:=(∀ y,0≤E y)∧(∀ y,y∉cuspSet k L D X x→ E y=0)∧componentAlpha k L D X H x a≠0∧(∃ ι:Type,z30 (nf q5 (qK) ι))∧∀ (ι:Type) (C:nf q5 (qK) ι), MatchesSectionOrder q5 (qK) C (componentAlpha k L D X H x a) (2•E)
ec 1 open ArithmeticThetaIsogenyHalfLinesR0193
section rc variable (k:Type) [z1 k] [z2 k] (L m:ℕ) (D:ld k L) (X:q1) (H:ex k L D X)
def P506.HalfBranch(x:vS)(A:DivisorLine q5)(β:tp q5 A.line 2≅hodge k L D X x H):Prop:=∀ (V:DiskTest k L D X) (ζ:k),IsPrimitiveRoot ζ L→ CanonicalMarking k L ζ V.level→ ∀ (f:Disk k⟶Component k L D X x) (hf:f≫inclusion k L D X x=V.disk) (η:Γ(q29,⊤)),ExtendsGenerator k L H V η→ ∃ h:Γ((zPB f).obj A.line,⊤),IsFrame ((zPB f).obj A.line) ⊤ h∧pullbackGlobalSection f A.line A.section_=scalar (z4 k) (thetaAt k (L*m))•h∧ (diskHodgeIso k L D X x H V f hf).hom.app ⊤ (((P505.powerComparison _ _ f A.line 2).symm≪≫(zPB f).mapIso β).hom.app ⊤ (tensorPowerSection _ ((zPB f).obj A.line) 2 ⊤ h))=η
end
section rc
structure ArithmeticThetaSquareLinesR0192.SquareLine(Z:zS)(W:Z.Modules) where (line:Z.Modules) (invertible:wT line) (square:tp Z line 2≅W)
end
namespace ArithmeticThetaSimultaneousUnaryR0187 rc
abbrev Sections(B:zS)(J:B.Modules):=J.presheaf.obj (xI ⊤)
def unarySeries(k:Type)[z1 k](N m:ℕ)(ν:ℤ):z4 k:=z4.map (Int.castRingHom k) (z4.subst (z4.X ^ (N^2/m)) (wQ m ν))
structure RootCover(k:Type)[z1 k](B:zS)(b:B⟶Spec (zCR k))(bound:ℕ) where (space:zS) (map:space⟶B) (integral:IsIntegral space) (finite:IsFinite map) (flat:Flat map) (surjective:Surjective map) (proper:IsProper (map≫b)) (smooth:SmoothOfRelativeDimension 1 (map≫b)) (degree:∀ x:B,0 < map.finrank x∧map.finrank x≤bound)
ec 1 open ArithmeticThetaSimultaneousUnaryR0187
section rc
def ArithmeticThetaCommonHalfHodgeR0185.along{Z Y B:Scheme}(g:Z⟶Y)(p:Y⟶B)(f:Z⟶B)(h:g≫p=f)(M:B.Modules):(zPB g).obj ((zPB p).obj M)≅(zPB f).obj M:=(zPC g p).app M≪≫(zS.Modules.pullbackCongr h).app M end
section rc
def ArithmeticThetaSharpCoverR0194.RationalExpansion(k:Type)[z1 k](Z:zS)[IsIntegral Z](f:Puncture k⟶Z)(r:Z.functionField)(a:z5 k):Prop:=
  ∃ (U:Z.Opens) (hU:z30 U),letI:=hU
    ∃ v:Z.presheaf.obj (qI),
      (Z.germToFunctionField U) v=r∧
      f ⁻¹ᵁ U=⊤∧
      f.app U v=(Puncture k).presheaf.map
        (homOfLE (show f ⁻¹ᵁ U≤⊤ from le_top)).op
        (scalar (z5 k) a)
end
open ArithmeticThetaSharpCoverR0194 namespace P529 rc
def squarePull{Z Y:Scheme}{W:Z.Modules}(f:Y⟶Z)(A:SquareLine Z W):tp Y ((zPB f).obj A.line) 2≅(zPB f).obj W:=(P505.powerComparison Y Z f A.line 2).symm≪≫(zPB f).mapIso A.square
def squareOnDisk(k:Type)[z1 k]{B X:zS}(p:B⟶X)(J:B.Modules)(H:vB)(β:tp B J 2≅(zPB p).obj H)(f:Disk k⟶B)(d:Disk k⟶X)(hf:f≫p=d):tp (Disk k) ((zPB f).obj J) 2≅(zPB d).obj H:=(P505.powerComparison (Disk k) B f J 2).symm≪≫ (zPB f).mapIso β≪≫along f p d hf H
def pullbackPowerSection{Y X:Scheme.{u}}(p:Y⟶X)(H:vB)(n:ℕ)(F:Γ(tp X H n,⊤)):Γ(tp Y ((zPB p).obj H) n,⊤):=(P505.powerComparison Y X p H n).hom.app (p ⁻¹ᵁ (⊤:vH)) (pullbackGlobalSection p (tp X H n) F)
ec 1 open P529
section rc
structure P529.CoverFrame(k:Type)[z1 k][z2 k](N:ℕ){D:q27}{X:q12}(H:q23)(V:q25)(J:SquareLine q30 (hodge k (level N) D X q4 H))(b:ℕ)(C:RootCover k q30 (projection k (level N) D X q4) b) where (disk:Disk k⟶C.space) (triangle:disk≫(xH≫q34)=V.disk) (dominant:IsDominant (genericInclusion k≫disk)) (frame:Sections (Disk k) ((zPB disk).obj q26)) (isFrame:IsFrame _ ⊤ frame) (generator:Sections (Disk k) (q29)) (extendsGenerator:ExtendsGenerator k (level N) H V generator) (square_eq:(squareOnDisk k (xH≫q34) q26 vM (squarePull xH J≪≫(zPC xH (q34)).app vM) disk V.disk triangle).hom.app ⊤ (tensorPowerSection _ _ 2 ⊤ frame)=generator)
end
namespace P534 rc
structure CanonicalHalf(k:Type)[z1 k][z2 k](L m:ℕ)(D:ld k L)(X:q1)(H:ex k L D X)(x:vS) where (openData:OpenAlpha k L m D) (alpha:Γ(vM,⊤)) (realizes:CompactRealizes k L m D X H openData alpha) (divisor:Component k L D X x→₀ ℤ) (effective:∀ y,0≤divisor y) (normal:NormalAffine q5) (half:HalfDivisor k L D X H x alpha divisor) (invertible:wT (q6).line) (square:tp q5 (q6).line 2≅hodge k L D X x H) (square_section:square.hom.app ⊤ (tensorPowerSection _ (q6).line 2 ⊤ (q6).section_)=componentAlpha k L D X H x alpha) (branch:P506.HalfBranch k L m D X H x q6 square)
variable {k:Type} [z1 k] [z2 k] {L m:ℕ} {D:ld k L} {X:q1} {H:ex k L D X} {x:vS}
def CanonicalHalf.data(A:CanonicalHalf k L m D X H x):DivisorLine q5:=canonicalDivisorData k L D X x A.divisor A.effective A.normal
def CanonicalHalf.squareLine(A:CanonicalHalf k L m D X H x):SquareLine q5 (qK):=⟨A.data.line,A.invertible,A.square⟩
ec 1 namespace P534 rc
def IsSquarePower{B X:Scheme}(p:B⟶X)(J:B.Modules)(H:vB)(β:tp B J 2≅(zPB p).obj H)(N:ℕ)(e:tp B J (exponent N)≅tp B ((zPB p).obj H) (weight N)):Prop:=∀ (U:B.Opens) (v:J.presheaf.obj (qI)),e.hom.app U (tensorPowerSection B J (exponent N) U v)= tensorPowerSection B ((zPB p).obj H) (weight N) U (β.hom.app U (tensorPowerSection B J 2 U v))
def UnaryPowers(k:Type)[z1 k][z2 k](N s:ℕ)(m:Fin s→ ℕ)(ν:Fin s→ ℤ){D:q27}{X:q12}(H:q23){B:zS}(p:B⟶vS)(J:B.Modules)(β:tp B J 2≅(zPB p).obj vM)(F:Fin s→ Sections B (tp B J (exponent N))):Prop:= ∃ e:tp B J (exponent N)≅tp B ((zPB p).obj vM) (weight N),IsSquarePower p J vM β N e∧∀ j,F j≠0∧∃ (a b:Fin N),a.val=unaryResidue (m j) N (ν j)∧b.val=N/2∧∃ (A:P514.OpenPower k (m j) N D a b) (t:Sections vS (q56)), P514.RealizesUnary k (m j) N H (ν j) A t∧e.hom.app ⊤ (F j)=pullbackPowerSection p vM (weight N) t
ec 1 namespace P534 rc
def RatioMultiple{B Y:Scheme}[IsIntegral B](p:Y⟶B)(J:wB)(t t₀:Sections Y J)(r:B.functionField):Prop:=
  ∃ (U:B.Opens) (hU:z30 U),letI:=hU
    ∃ v:B.presheaf.obj (qI),B.germToFunctionField U v=r∧
      q62=
        p.app U v•J.presheaf.map (homOfLE (show p ⁻¹ᵁ U≤⊤ from le_top)).op t₀
def RegularUnary(k:Type)[z1 k][z2 k](N s:ℕ)(m:Fin s→ ℕ)(ν:Fin s→ ℤ){D:q27}{X:q12}(H:q23)(V:q25)(J:SquareLine q30 (hodge k (level N) D X q4 H))(b:ℕ)(C:RootCover k q30 (projection k (level N) D X q4) b)(F:CoverFrame k N H V J b C)(t₀:Fin s→ Sections C.space q26):Prop:= ∃ t:Fin s→ Sections C.space q26,UnaryPowers k N s m ν H (xH≫q34) q26 (squarePull xH J≪≫(zPC xH (q34)).app vM) (fun i=> tensorPowerSection _ _ (exponent N) ⊤ (t i))∧∀ i,t i≠0∧pullbackGlobalSection F.disk q26 (t i)=scalar (z4 k) (unarySeries k N (m i) (ν i))•F.frame∧∃ r:(q30).functionField,RationalExpansion k _ (genericInclusion k≫(F.disk≫xH)) r (q2 (unarySeries k N (m i) (ν i))/q2 (unarySeries k N (m i) 0))∧RatioMultiple xH q26 (t i) (t₀ i) r
ec 1
section rc
def P534.CommonUnary(k:Type)[z1 k][z2 k](N s:ℕ)(m:Fin (s+1)→ ℕ)(ν:Fin (s+1)→ ℤ)(D:q27)(X:q12)(H:q23)(V:q25):Prop:=
  let x:=V.disk (closedPoint k)
  ∃ A:∀ i,CanonicalHalf k (level N) (m i) D X H x,
    ∃ C:RootCover k (Component k (level N) D X x)
      (projection k (level N) D X x) (2^s),
      Etale xH∧(s=0→ IsIso xH)∧
      ∃ F:CoverFrame k N H V (A 0).squareLine (2^s) C,
        ∃ t₀:Fin (s+1)→ Sections C.space
          ((zPB xH).obj (A 0).data.line),
          (∀ i,t₀ i≠0∧
            pullbackGlobalSection F.disk ((zPB xH).obj (A 0).data.line)
              (t₀ i)=scalar (z4 k)
                (unarySeries k N (m i) 0)•F.frame)∧
          RegularUnary k N (s+1) m ν H V (A 0).squareLine (2^s) C F t₀
end
section rc
theorem P534.arithmeticCommonUnary:∀ (k:Type) [z1 k] [z2 k] (N s:ℕ),0 < N→ Even N→ ∀ (m:Fin (s+1)→ ℕ) (ν:Fin (s+1)→ ℤ),(∀ i,0 < m i∧Even (m i)∧m i ∣ N∧(-(m i:ℤ)≤2*ν i∧2*ν i < (m i:ℤ)))→ ∀ (D:q27) (X:q12) (H:q23),ca k (level N) H→ P519.Boundary.GeometricallyCanonical H→ ∀ (V:q25) (ζ:k),IsPrimitiveRoot ζ (level N)→ CanonicalMarking k (level N) ζ V.level→ P534.CommonUnary k N s m ν D X H V:=by sorry end
