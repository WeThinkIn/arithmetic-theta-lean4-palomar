module

public import SplitCyclicKernelR0173
public import PointedRelativeGroupHomR0173
public import Definitions.Def_JacJ1Iface
public import RelativeCyclicQuotientDefinitionsR0173

@[expose] public section

/-! Definitions for recovering the quotient presentation. Each field is an
actual map or a specified geometric predicate. The first obligation constructs
all these data from the original cyclic section, including the Hodge frame.
No presentation or equation is supplied as a premise to that construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCyclicPresentationR0174
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeCyclicQuotientR0173

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
variable {n : ℕ} (P : CyclicSection R W G n)

structure FramedQuotient where
  target : Scheme.{u}
  structureMap : target ⟶ Base R
  law : GoodReductionJacobian.RelativeGroupLaw R structureMap
  map : Curve R W ⟶ target
  over_eq : map ≫ structureMap = ArithmeticThetaRelativeKatoR0169.structureMap R W
  geometry : GoodReductionJacobian.AbelianSchemePropertyBundle R structureMap
  dimension : SmoothOfRelativeDimension 1 structureMap
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  degree : ∀ y, map.finrank y = n
  origin_eq : origin R W ≫ map = (law.one (𝟙 (Base R))).val
  kernel : ((law.one (𝟙 (Base R))).val).ker.comap map = kernelIdeal R W G P
  hodge : Nonempty ((SheafOfModules.unit (Base R).ringCatSheaf : (Base R).Modules) ≅
    (Scheme.Modules.pullback (law.one (𝟙 (Base R))).val).obj structureMap.kaehler)

end ArithmeticThetaCyclicPresentationR0174
