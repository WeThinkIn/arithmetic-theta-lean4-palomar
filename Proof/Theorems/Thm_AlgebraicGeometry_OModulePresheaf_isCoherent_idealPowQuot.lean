module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFc : F.IsCoherent) : (OModulePresheaf.idealPowQuot π I F k).IsCoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.solution
