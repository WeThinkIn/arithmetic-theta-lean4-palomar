import NormalizedSectionDefinitions
import LocalFrameBridge

open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaLineRoot

universe u
noncomputable section

namespace ArithmeticThetaNormalizedSections

/-- Restrict a genuine local frame to a smaller open, retaining naturality on all subopens. -/
def restrictLocalFrame (X : Scheme.{u}) (H : X.Modules) (U V : X.Opens)
    (hVU : V ≤ U) (e : LocalFrame X H U) : LocalFrame X H V where
  equiv W hWV := e.equiv W (hWV.trans hVU)
  naturality W Z hZW hWV a := e.naturality W Z hZW (hWV.trans hVU) a

/-- A locally trivial line has a normal affine frame cover indexed by the actual points. -/
theorem exists_normalFrameCover (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (hN : NormalAffine X) (hH : IsLineBundle X H) :
    Nonempty (NormalFrameCover X H X) := by
  classical
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (LocalFrame X H V) := by
    intro x
    obtain ⟨U, hxU, ⟨e⟩⟩ := hH x
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    exact ⟨V, hxV, hV, ⟨restrictLocalFrame X H U V hVU (localFrameOfIso X H U e)⟩⟩
  choose V hxV hV e using hlocal
  refine ⟨{
    opens := V
    covers := ?_
    nonempty := fun x ↦ ⟨⟨x, hxV x⟩⟩
    affine := hV
    normal := ?_
    frame := fun x ↦ Classical.choice (e x)
  }⟩
  · intro x _
    exact (show V x ≤ iSup V from le_iSup V x) (hxV x)
  · intro x
    let : Nonempty (V x) := ⟨⟨x, hxV x⟩⟩
    exact hN (V x) (hV x)

end ArithmeticThetaNormalizedSections
