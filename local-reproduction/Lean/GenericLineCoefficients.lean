import NormalizedSectionDefinitions
import LocalFrameBridge

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot

universe u

noncomputable section

namespace ArithmeticThetaNormalizedSections

/-- Restriction inside a genuine frame is injective when the smaller open is nonempty. -/
theorem frame_restriction_injective (X : Scheme.{u}) [IsIntegral X]
    (H : X.Modules) (U V : X.Opens) [Nonempty V]
    (e : LocalFrame X H U) (hVU : V ≤ U) :
    Function.Injective (H.presheaf.map (homOfLE hVU).op) := by
  intro s t h
  apply (e.equiv U le_rfl).symm.injective
  apply map_injective_of_isIntegral X (homOfLE hVU)
  apply (e.equiv V hVU).injective
  simpa only [← e.naturality U V hVU le_rfl, LinearEquiv.apply_symm_apply] using h

/-- A global section is determined by its generic coefficient in any nonempty local frame. -/
theorem sectionCoefficient_injective (X : Scheme.{u}) [IsIntegral X]
    (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) :
    Function.Injective (sectionCoefficient X H U e) := by
  classical
  intro s t h
  have hU : H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t := by
    apply (e.equiv U le_rfl).symm.injective
    exact X.germToFunctionField_injective U h
  choose V hx E using hH
  let frame (x : X) : LocalFrame X H (V x) := localFrameOfIso X H (V x) (E x).some
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩ V ⊤
    (fun _ ↦ homOfLE le_top) hcover
  intro x
  let : Nonempty (V x) := ⟨⟨x, hx x⟩⟩
  let : Nonempty (V x ⊓ U : X.Opens) := overlap_nonempty X (V x) U
  apply frame_restriction_injective X H (V x) (V x ⊓ U) (frame x) inf_le_left
  have hW := congrArg
    (H.presheaf.map (homOfLE (inf_le_right : V x ⊓ U ≤ U)).op) hU
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, homOfLE_comp] using hW

end ArithmeticThetaNormalizedSections
