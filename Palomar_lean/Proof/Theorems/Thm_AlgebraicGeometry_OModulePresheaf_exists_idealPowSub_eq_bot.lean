module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (U : V.affineOpens) : ∃ N : ℕ, OModulePresheaf.idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.solution
