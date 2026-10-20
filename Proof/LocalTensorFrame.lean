module

public import ActualSheafTensor

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
open ArithmeticThetaLineRoot

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaSheafTensor

variable (X : Scheme.{u}) (H K : X.Modules) (U : X.Opens)

def presheafOver : X.PresheafOfModules ⥤
    PresheafOfModules.{u} (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj

def tensorFramePreIso (e : LocalFrame X H U) (f : LocalFrame X K U) :
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val ≅
      (presheafOver X U).obj (tensorPresheaf X H K) :=
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

def localTensorTrivializationHom (e : LocalFrame X H U) (f : LocalFrame X K U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.over (sheafTensor X H K) U :=
  ⟨(tensorFramePreIso X H K U e f).hom ≫
    (presheafOver X U).map (tensorUnitMap X H K)⟩

theorem localTensorTrivializationHom_isIso (e : LocalFrame X H U) (f : LocalFrame X K U) :
    IsIso (localTensorTrivializationHom X H K U e f) := by
  let J := Opens.grothendieckTopology X
  let η := CategoryTheory.toSheafify J (tensorPresheaf X H K).presheaf
  let e' := (PresheafOfModules.toPresheaf _).mapIso (tensorFramePreIso X H K U e f)
  let ηU := Functor.whiskerLeft (Over.forget U).op η
  have hinj : Presheaf.IsLocallyInjective (J.over U) ηU :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) η
  have hsurj : Presheaf.IsLocallySurjective (J.over U) ηU :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) η
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (X.ringCatSheaf.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective (J.over U) (e'.hom ≫ ηU)
    infer_instance
  · change Presheaf.IsLocallySurjective (J.over U) (e'.hom ≫ ηU)
    infer_instance

def localTensorTrivialization (e : LocalFrame X H U) (f : LocalFrame X K U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      SheafOfModules.over (sheafTensor X H K) U :=
  have := localTensorTrivializationHom_isIso X H K U e f
  asIso (localTensorTrivializationHom X H K U e f)

def tensorFrame (e : LocalFrame X H U) (f : LocalFrame X K U) :
    LocalFrame X (sheafTensor X H K) U :=
  localFrameOfIso X (sheafTensor X H K) U (localTensorTrivialization X H K U e f)

theorem tensorFrame_apply (e : LocalFrame X H U) (f : LocalFrame X K U)
    (V : X.Opens) (hVU : V ≤ U) (a : Γ(X, V)) :
    (tensorFrame X H K U e f).equiv V hVU a =
      tensorSection X H K V (e.equiv V hVU 1) (f.equiv V hVU a) := rfl

theorem tensorSection_frame (e : LocalFrame X H U) (f : LocalFrame X K U)
    (V : X.Opens) (hVU : V ≤ U) (a b : Γ(X, V)) :
    tensorSection X H K V (e.equiv V hVU a) (f.equiv V hVU b) =
      (tensorFrame X H K U e f).equiv V hVU (a * b) := by
  rw [tensorFrame_apply]
  apply congrArg ((tensorUnitMap X H K).app (op V))
  have hea : e.equiv V hVU a = a • e.equiv V hVU 1 := by
    simpa using (e.equiv V hVU).map_smul a (1 : Γ(X, V))
  rw [hea, TensorProduct.smul_tmul]
  congr 1
  exact ((f.equiv V hVU).map_smul a b).symm

theorem tensorFrame_transition (U' : X.Opens)
    (e : LocalFrame X H U) (e' : LocalFrame X H U')
    (f : LocalFrame X K U) (f' : LocalFrame X K U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition ((tensorFrame X H K U e f).equiv V hVU)
      ((tensorFrame X H K U' e' f').equiv V hVU') =
      transition (e.equiv V hVU) (e'.equiv V hVU') *
        transition (f.equiv V hVU) (f'.equiv V hVU') := by
  apply ((tensorFrame X H K U e f).equiv V hVU).injective
  rw [transition, LinearEquiv.apply_symm_apply, tensorFrame_apply,
    transition_apply (e.equiv V hVU) (e'.equiv V hVU'),
    transition_apply (f.equiv V hVU) (f'.equiv V hVU'), mul_one, mul_one]
  exact tensorSection_frame X H K U e f V hVU _ _

theorem tensorFrame_transitionUnit (U' : X.Opens)
    (e : LocalFrame X H U) (e' : LocalFrame X H U')
    (f : LocalFrame X K U) (f' : LocalFrame X K U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transitionUnit ((tensorFrame X H K U e f).equiv V hVU)
      ((tensorFrame X H K U' e' f').equiv V hVU') =
      transitionUnit (e.equiv V hVU) (e'.equiv V hVU') *
        transitionUnit (f.equiv V hVU) (f'.equiv V hVU') := by
  apply Units.ext
  exact tensorFrame_transition X H K U U' e e' f f' V hVU hVU'

end ArithmeticThetaSheafTensor
