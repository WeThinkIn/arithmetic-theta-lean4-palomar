module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) {Y : TopologicalSpace.Closeds V} (hFs : F.SupportedIn Y) : (OModulePresheaf.idealPowQuot π I F k).SupportedIn Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot.solution
