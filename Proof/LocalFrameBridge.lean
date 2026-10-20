module

public import LineRootFoundations

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaLineRoot

variable (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)

/-- Extract the natural section-level trivialization from a genuine local module-sheaf iso. -/
def localFrameOfIso (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
    SheafOfModules.over H U) : LocalFrame X H U where
  equiv V hVU :=
    (CategoryTheory.Iso.toLinearEquiv
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE hVU)))).mapIso e))
  naturality V W hWV hVU a := by
    let f : Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU) :=
      Over.homMk (homOfLE hWV)
    exact (PresheafOfModules.naturality_apply e.hom.val f.op a).symm

theorem localFrameOfIso_apply (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
    SheafOfModules.over H U) (V : X.Opens) (hVU : V ≤ U) (a : Γ(X, V)) :
    (localFrameOfIso X H U e).equiv V hVU a =
      e.hom.val.app (op (Over.mk (homOfLE hVU))) a := rfl

/-- Bundle natural rank-one section equivalences back into a genuine sheaf isomorphism. -/
def localFrameIso (e : LocalFrame X H U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ SheafOfModules.over H U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ (e.equiv V.unop.left V.unop.hom.le).toModuleIso)
      (fun {V W} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (e.naturality V.unop.left W.unop.left f.unop.left.le V.unop.hom.le a).symm))

theorem localFrameIso_apply (e : LocalFrame X H U)
    (V : X.Opens) (hVU : V ≤ U) (a : Γ(X, V)) :
    (localFrameIso X H U e).hom.val.app (op (Over.mk (homOfLE hVU))) a =
      e.equiv V hVU a := rfl

theorem localFrameOfIso_iso (e : LocalFrame X H U) :
    localFrameOfIso X H U (localFrameIso X H U e) = e := by
  cases e
  rfl

theorem localFrameIso_ofIso (e : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
    SheafOfModules.over H U) :
    localFrameIso X H U (localFrameOfIso X H U e) = e := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end ArithmeticThetaLineRoot
